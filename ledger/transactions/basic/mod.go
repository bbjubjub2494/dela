// Package basic implements a kind of transaction that includes a signature and
// a nonce so that it can prevent replay attacks. Access control can also be
// enforced from the identity of the transaction.
//
// The action defines how the transaction will be consumed and it follows the
// same separation logic with a client and a server side. The client only
// creates the action with its arguments and the server will decorate it to
// consume it.
package basic

import (
	"encoding/binary"
	"fmt"
	"io"

	"github.com/golang/protobuf/proto"
	"github.com/golang/protobuf/ptypes/any"
	"go.dedis.ch/fabric/crypto"
	"go.dedis.ch/fabric/crypto/common"
	"go.dedis.ch/fabric/encoding"
	"go.dedis.ch/fabric/ledger/arc"
	"go.dedis.ch/fabric/ledger/inventory"
	"go.dedis.ch/fabric/ledger/transactions"
	"golang.org/x/xerrors"
)

//go:generate protoc -I ./ --go_out=./ ./messages.proto

// TODO: rename action to task

// ClientAction is used to create a transaction.
type ClientAction interface {
	encoding.Packable
	encoding.Fingerprinter
}

// Context is the context provided to a server transaction when consumed.
type Context interface {
	// GetID returns the unique identifier of the transaction.
	GetID() []byte

	// GetIdentity returns the identity who signed the transaction.
	GetIdentity() arc.Identity
}

// ServerAction provides the primitives to consume a specialization of a
// transaction.
type ServerAction interface {
	ClientAction

	Consume(Context, inventory.WritablePage) error
}

// ActionFactory provide the primitives to instantiate an action from its
// protobuf message.
type ActionFactory interface {
	FromProto(proto.Message) (ServerAction, error)
}

// transaction is an atomic execution.
//
// - implements transactions.ClientTransaction
type transaction struct {
	hash      []byte
	nonce     uint64
	identity  crypto.PublicKey
	signature crypto.Signature
	action    ClientAction
}

// GetID implements transactions.ClientTransaction. It returns the unique
// identifier of the transaction.
func (t transaction) GetID() []byte {
	return t.hash[:]
}

// GetIdentity implements basic.Context. It returns the identity who signed the
// transaction.
func (t transaction) GetIdentity() arc.Identity {
	return t.identity
}

// Pack implements encoding.Packable. It returns the protobuf message of the
// transaction.
func (t transaction) Pack(enc encoding.ProtoMarshaler) (proto.Message, error) {
	pb := &TransactionProto{
		Nonce: t.nonce,
	}

	var err error
	pb.Identity, err = enc.PackAny(t.identity)
	if err != nil {
		return nil, xerrors.Errorf("couldn't pack identity: %v", err)
	}

	pb.Signature, err = enc.PackAny(t.signature)
	if err != nil {
		return nil, xerrors.Errorf("couldn't pack signature: %v", err)
	}

	pb.Action, err = enc.PackAny(t.action)
	if err != nil {
		return nil, xerrors.Errorf("couldn't pack action: %v", err)
	}

	return pb, nil
}

// Fingerprint implements encoding.Fingerprinter. It serializes the transaction
// into the writer in a deterministic way.
func (t transaction) Fingerprint(w io.Writer, enc encoding.ProtoMarshaler) error {
	buffer := make([]byte, 8)
	binary.LittleEndian.PutUint64(buffer[:], t.nonce)

	_, err := w.Write(buffer)
	if err != nil {
		return xerrors.Errorf("couldn't write nonce: %v", err)
	}

	buffer, err = t.identity.MarshalBinary()
	if err != nil {
		return xerrors.Errorf("couldn't marshal identity: %v", err)
	}

	_, err = w.Write(buffer)
	if err != nil {
		return xerrors.Errorf("couldn't write identity: %v", err)
	}

	err = t.action.Fingerprint(w, enc)
	if err != nil {
		return xerrors.Errorf("couldn't write action: %v", err)
	}

	return nil
}

// String implements fmt.Stringer. It returns a string representation of the
// transaction.
func (t transaction) String() string {
	return fmt.Sprintf("Transaction[%v]", t.identity)
}

// serverTransaction is an extension of the transaction that can be consumed.
//
// - implements transactions.ServerTransaction
type serverTransaction struct {
	transaction
}

// Consume implements transactions.ServerTransaction. It first insures the nonce
// is correct and writes the new one into the page. It then consumes the action
// of the transaction.
func (t serverTransaction) Consume(page inventory.WritablePage) error {
	// TODO: consume nonce

	action, ok := t.action.(ServerAction)
	if !ok {
		return xerrors.Errorf("action must implement 'basic.ServerAction'")
	}

	err := action.Consume(t, page)
	if err != nil {
		return xerrors.Errorf("couldn't consume action: %v", err)
	}

	return nil
}

// TransactionFactory is an implementation of a Byzcoin transaction factory.
//
// - implements ledger.TransactionFactory
type TransactionFactory struct {
	signer           crypto.Signer
	hashFactory      crypto.HashFactory
	publicKeyFactory crypto.PublicKeyFactory
	signatureFactory crypto.SignatureFactory
	actionFactory    ActionFactory
	encoder          encoding.ProtoMarshaler
}

// NewTransactionFactory returns a new instance of the transaction factory.
func NewTransactionFactory(signer crypto.Signer, f ActionFactory) TransactionFactory {
	return TransactionFactory{
		signer:           signer,
		hashFactory:      crypto.NewSha256Factory(),
		publicKeyFactory: common.NewPublicKeyFactory(),
		signatureFactory: common.NewSignatureFactory(),
		actionFactory:    f,
		encoder:          encoding.NewProtoEncoder(),
	}
}

// New returns a new transaction from the given action. The transaction will be
// signed.
func (f TransactionFactory) New(action ClientAction) (transactions.ClientTransaction, error) {
	tx := transaction{
		nonce:    0, // TODO: monotonic nonce
		identity: f.signer.GetPublicKey(),
		action:   action,
	}

	h := f.hashFactory.New()
	err := tx.Fingerprint(h, f.encoder)
	if err != nil {
		return tx, xerrors.Errorf("couldn't compute hash: %v", err)
	}

	tx.hash = h.Sum(nil)

	tx.signature, err = f.signer.Sign(tx.hash)
	if err != nil {
		return tx, xerrors.Errorf("couldn't sign tx: %v", err)
	}

	return tx, nil
}

// FromProto implements ledger.TransactionFactory. It returns a new transaction
// built from the protobuf message.
func (f TransactionFactory) FromProto(in proto.Message) (transactions.ServerTransaction, error) {
	var pb *TransactionProto

	switch msg := in.(type) {
	case *any.Any:
		pb = &TransactionProto{}
		err := f.encoder.UnmarshalAny(msg, pb)
		if err != nil {
			return nil, xerrors.Errorf("couldn't unmarshal input: %v", err)
		}
	case *TransactionProto:
		pb = msg
	default:
		return nil, xerrors.Errorf("invalid transaction type '%T'", in)
	}

	action, err := f.actionFactory.FromProto(pb.GetAction())
	if err != nil {
		return nil, xerrors.Errorf("couldn't decode action: %v", err)
	}

	tx := serverTransaction{
		transaction: transaction{
			nonce:  pb.GetNonce(),
			action: action,
		},
	}

	err = f.fillIdentity(&tx, pb)
	if err != nil {
		return nil, err
	}

	return tx, nil
}

func (f TransactionFactory) fillIdentity(tx *serverTransaction, pb *TransactionProto) error {
	identity, err := f.publicKeyFactory.FromProto(pb.GetIdentity())
	if err != nil {
		return xerrors.Errorf("couldn't decode public key: %v", err)
	}

	signature, err := f.signatureFactory.FromProto(pb.GetSignature())
	if err != nil {
		return xerrors.Errorf("couldn't decode signature: %v", err)
	}

	tx.identity = identity
	tx.signature = signature

	h := f.hashFactory.New()
	err = tx.Fingerprint(h, f.encoder)
	if err != nil {
		return xerrors.Errorf("couldn't compute hash: %v", err)
	}

	tx.hash = h.Sum(nil)

	err = tx.identity.Verify(tx.hash, tx.signature)
	if err != nil {
		return xerrors.Errorf("signature does not match tx: %v", err)
	}

	return nil
}
