package bls

import (
	"bytes"

	"github.com/golang/protobuf/proto"
	"github.com/golang/protobuf/ptypes/any"
	"go.dedis.ch/fabric/crypto"
	"go.dedis.ch/fabric/encoding"
	"go.dedis.ch/kyber/v3"
	"go.dedis.ch/kyber/v3/pairing"
	"go.dedis.ch/kyber/v3/sign/bls"
	"go.dedis.ch/kyber/v3/util/key"
	"golang.org/x/xerrors"
)

//go:generate protoc -I ./ --go_out=./ ./messages.proto

var (
	suite = pairing.NewSuiteBn256()

	protoenc encoding.ProtoMarshaler = encoding.NewProtoEncoder()
)

// publicKey can be provided to verify a BLS signature.
type publicKey struct {
	point kyber.Point
}

// MarshalBinary implements encoding.BinaryMarshaler. It produces a slice of
// bytes representing the public key.
func (pk publicKey) MarshalBinary() ([]byte, error) {
	return pk.point.MarshalBinary()
}

// Pack implements encoding.Packable. It returns the protobuf message
// representing the public key.
func (pk publicKey) Pack(encoding.ProtoMarshaler) (proto.Message, error) {
	buffer, err := pk.point.MarshalBinary()
	if err != nil {
		return nil, encoding.NewEncodingError("point", err)
	}

	return &PublicKeyProto{Data: buffer}, nil
}

// Equal implements crypto.PublicKey. It returns true if the other public key
// is the same.
func (pk publicKey) Equal(other crypto.PublicKey) bool {
	pubkey, ok := other.(publicKey)
	if !ok {
		return false
	}

	return pubkey.point.Equal(pk.point)
}

// signature is a proof of the integrity of a single message associated with a
// unique public key.
type signature struct {
	data []byte
}

// MarshalBinary implements encoding.BinaryMarshaler. It returns a slice of
// bytes representing the signature.
func (sig signature) MarshalBinary() ([]byte, error) {
	return sig.data, nil
}

// Pack implements encoding.Packable. It returns  the protobuf message
// representing the signature.
func (sig signature) Pack(encoding.ProtoMarshaler) (proto.Message, error) {
	return &SignatureProto{Data: sig.data}, nil
}

// Equal implements crypto.PublicKey.
func (sig signature) Equal(other crypto.Signature) bool {
	otherSig, ok := other.(signature)
	if !ok {
		return false
	}

	return bytes.Equal(sig.data, otherSig.data)
}

// publicKeyFactory creates BLS compatible public key from protobuf messages.
type publicKeyFactory struct{}

// FromProto implements crypto.PublicKeyFactory. It creates a public key from
// its protobuf representation.
func (f publicKeyFactory) FromProto(src proto.Message) (crypto.PublicKey, error) {
	var pb *PublicKeyProto

	switch msg := src.(type) {
	case *PublicKeyProto:
		pb = msg
	case *any.Any:
		pb = &PublicKeyProto{}

		err := protoenc.UnmarshalAny(msg, pb)
		if err != nil {
			return nil, encoding.NewAnyDecodingError(pb, err)
		}
	default:
		return nil, xerrors.Errorf("invalid public key type '%T'", src)
	}

	point := suite.Point()
	err := point.UnmarshalBinary(pb.GetData())
	if err != nil {
		return nil, xerrors.Errorf("failed to unmarshal point: %v", err)
	}

	return publicKey{point: point}, nil
}

// signatureFactory provides functions to create BLS signatures from protobuf
// messages.
type signatureFactory struct{}

// FromProto implements crypto.SignatureFactory. It creates a BLS signature from
// its protobuf representation.
func (f signatureFactory) FromProto(src proto.Message) (crypto.Signature, error) {
	var pb *SignatureProto

	switch msg := src.(type) {
	case *SignatureProto:
		pb = msg
	case *any.Any:
		pb = &SignatureProto{}

		err := protoenc.UnmarshalAny(msg, pb)
		if err != nil {
			return nil, encoding.NewAnyDecodingError(pb, err)
		}
	default:
		return nil, xerrors.Errorf("invalid signature type '%T'", src)
	}

	return signature{data: pb.GetData()}, nil
}

// verifier provides primitives to verify a BLS signature of a unique message.
type blsVerifier struct {
	points []kyber.Point
}

// NewVerifier returns a new verifier that can verify BLS signatures.
func newVerifier(points []kyber.Point) crypto.Verifier {
	return blsVerifier{points: points}
}

// Verify implements crypto.Verifier. It returns nil if the signature matches
// the message, or an error otherwise.
func (v blsVerifier) Verify(msg []byte, sig crypto.Signature) error {
	aggKey := bls.AggregatePublicKeys(suite, v.points...)

	err := bls.Verify(suite, aggKey, msg, sig.(signature).data)
	if err != nil {
		return err
	}

	return nil
}

type verifierFactory struct{}

// FromIterator implements crypto.VerifierFactory. It returns a verifier that
// will verify the signatures collectively signed by all the signers associated
// with the public keys.
func (v verifierFactory) FromIterator(iter crypto.PublicKeyIterator) (crypto.Verifier, error) {
	if iter == nil {
		return nil, xerrors.New("iterator is nil")
	}

	points := make([]kyber.Point, 0)
	for iter.HasNext() {
		next := iter.GetNext()
		pk, ok := next.(publicKey)
		if !ok {
			return nil, xerrors.Errorf("invalid public key type: %T", next)
		}

		points = append(points, pk.point)
	}

	return newVerifier(points), nil
}

// FromArray implements crypto.VerifierFactory. It returns a verifier that will
// verify the signatures collectively signed by all the signers associated with
// the public keys.
func (v verifierFactory) FromArray(publicKeys []crypto.PublicKey) (crypto.Verifier, error) {
	points := make([]kyber.Point, len(publicKeys))
	for i, pubkey := range publicKeys {
		pk, ok := pubkey.(publicKey)
		if !ok {
			return nil, xerrors.Errorf("invalid public key type: %T", pubkey)
		}

		points[i] = pk.point
	}

	return newVerifier(points), nil
}

type signer struct {
	keyPair *key.Pair
}

// NewSigner returns a new random BLS signer that supports aggregation.
func NewSigner() crypto.AggregateSigner {
	kp := key.NewKeyPair(suite)
	return signer{
		keyPair: kp,
	}
}

// GetVerifierFactory implements crypto.Signer. It returns the verifier factory
// for BLS signatures.
func (s signer) GetVerifierFactory() crypto.VerifierFactory {
	return verifierFactory{}
}

// GetPublicKeyFactory implements crypto.Signer. It returns the public key
// factory for BLS signatures.
func (s signer) GetPublicKeyFactory() crypto.PublicKeyFactory {
	return publicKeyFactory{}
}

// GetSignatureFactory implements crypto.Signer. It returns the signature
// factory for BLS signatures.
func (s signer) GetSignatureFactory() crypto.SignatureFactory {
	return signatureFactory{}
}

// GetPublicKey implements crypto.Signer. It returns the public key of the
// signer that can be used to verify signatures.
func (s signer) GetPublicKey() crypto.PublicKey {
	return publicKey{point: s.keyPair.Public}
}

// Sign implements crypto.Signer. It signs the message in parameter and returns
// the signature, or an error if it cannot sign.
func (s signer) Sign(msg []byte) (crypto.Signature, error) {
	sig, err := bls.Sign(suite, s.keyPair.Private, msg)
	if err != nil {
		return nil, xerrors.Errorf("couldn't make bls signature: %v", err)
	}

	return signature{data: sig}, nil
}

// Aggregate implements crypto.Signer. It aggregates the signatures into a
// single one that can be verifier with the aggregated public key associated.
func (s signer) Aggregate(signatures ...crypto.Signature) (crypto.Signature, error) {
	buffers := make([][]byte, len(signatures))
	for i, sig := range signatures {
		buffers[i] = sig.(signature).data
	}

	agg, err := bls.AggregateSignatures(suite, buffers...)
	if err != nil {
		return nil, xerrors.Errorf("couldn't aggregate: %v", err)
	}

	return signature{data: agg}, nil
}
