// Package simple implements a simple validation service.
package simple

import (
	"encoding/binary"

	"go.dedis.ch/dela/core/access"
	"go.dedis.ch/dela/core/execution"
	"go.dedis.ch/dela/core/store"
	"go.dedis.ch/dela/core/txn"
	"go.dedis.ch/dela/core/validation"
	"go.dedis.ch/dela/crypto"
	"golang.org/x/xerrors"
)

// Service is a standard validation service that will process the batch and
// update the snapshot accordingly.
//
// - implements validation.Service
type Service struct {
	execution execution.Service
	fac       validation.DataFactory
	hashFac   crypto.HashFactory
}

// NewService creates a new validation service.
func NewService(exec execution.Service, f txn.Factory) Service {
	return Service{
		execution: exec,
		fac:       NewDataFactory(f),
		hashFac:   crypto.NewSha256Factory(),
	}
}

// GetFactory implements validation.Service. It returns the factory for the
// validated data.
func (s Service) GetFactory() validation.DataFactory {
	return s.fac
}

// GetNonce reads the latest nonce in the storage for the given identity and
// returns the next valid nonce.
func (s Service) GetNonce(store store.Readable, ident access.Identity) (uint64, error) {
	if ident == nil {
		return 0, xerrors.New("missing identity in transaction")
	}

	key, err := s.keyFromIdentity(ident)
	if err != nil {
		return 0, xerrors.Errorf("key: %v", err)
	}

	value, err := store.Get(key)
	if err != nil {
		return 0, xerrors.Errorf("store: %v", err)
	}

	if value == nil || len(value) != 8 {
		return 0, nil
	}

	return binary.LittleEndian.Uint64(value) + 1, nil
}

// Validate implements validation.Service. It processes the list of transactions
// while updating the snapshot then returns a bundle of the transaction results.
func (s Service) Validate(store store.Snapshot, txs []txn.Transaction) (validation.Data, error) {
	results := make([]TransactionResult, len(txs))

	for i, tx := range txs {
		res := TransactionResult{tx: tx}

		err := s.validateTx(store, tx, &res)
		if err != nil {
			return nil, xerrors.Errorf("tx %#x: %v", tx.GetID()[:4], err)
		}

		results[i] = res
	}

	data := Data{
		txs: results,
	}

	return data, nil
}

func (s Service) validateTx(store store.Snapshot, tx txn.Transaction, r *TransactionResult) error {
	expectedNonce, err := s.GetNonce(store, tx.GetIdentity())
	if err != nil {
		return xerrors.Errorf("nonce: %v", err)
	}

	if expectedNonce != tx.GetNonce() {
		r.reason = "nonce is invalid"
		r.accepted = false
		return nil
	}

	res, err := s.execution.Execute(tx, store)
	if err != nil {
		// This is a critical error unrelated to the transaction itself.
		return xerrors.Errorf("failed to execute tx: %v", err)
	}

	r.reason = res.Message
	r.accepted = res.Accepted

	// Update the nonce associated to the identity so that this transaction
	// cannot be applied again.
	err = s.set(store, tx.GetIdentity(), tx.GetNonce())
	if err != nil {
		return xerrors.Errorf("failed to set nonce: %v", err)
	}

	return nil
}

func (s Service) set(store store.Snapshot, ident access.Identity, nonce uint64) error {
	key, err := s.keyFromIdentity(ident)
	if err != nil {
		return xerrors.Errorf("key: %v", err)
	}

	buffer := make([]byte, 8)
	binary.LittleEndian.PutUint64(buffer, nonce)

	err = store.Set(key, buffer)
	if err != nil {
		return xerrors.Errorf("store: %v", err)
	}

	return nil
}

func (s Service) keyFromIdentity(ident access.Identity) ([]byte, error) {
	data, err := ident.MarshalText()
	if err != nil {
		return nil, xerrors.Errorf("failed to marshal identity: %v", err)
	}

	h := s.hashFac.New()
	_, err = h.Write(data)
	if err != nil {
		return nil, xerrors.Errorf("failed to write identity: %v", err)
	}

	return h.Sum(nil), nil
}
