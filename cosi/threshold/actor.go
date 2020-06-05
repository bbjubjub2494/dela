package threshold

import (
	"context"

	"github.com/golang/protobuf/proto"
	"go.dedis.ch/dela"
	"go.dedis.ch/dela/cosi"
	"go.dedis.ch/dela/crypto"
	"go.dedis.ch/dela/encoding"
	"go.dedis.ch/dela/mino"
	"golang.org/x/xerrors"
)

// thresholdActor is an implementation of the cosi.Actor interface for a
// threshold collective signing.
//
// - implements cosi.Actor
type thresholdActor struct {
	*CoSi
	me      mino.Address
	rpc     mino.RPC
	reactor cosi.Reactor
}

// Sign implements cosi.Actor. It returns the collective signature from the
// collective authority, or an error if it failed.
func (a thresholdActor) Sign(ctx context.Context, msg encoding.Packable,
	ca crypto.CollectiveAuthority) (crypto.Signature, error) {

	innerCtx, cancel := context.WithCancel(context.Background())
	defer cancel()

	sender, rcvr, err := a.rpc.Stream(innerCtx, ca)
	if err != nil {
		return nil, xerrors.Errorf("couldn't open stream: %v", err)
	}

	req, err := a.encoder.Pack(msg)
	if err != nil {
		return nil, xerrors.Errorf("couldn't pack message: %v", err)
	}

	digest, err := a.reactor.Invoke(a.me, req)
	if err != nil {
		return nil, err
	}

	// The aggregated signature needs to include at least a threshold number of
	// signatures.
	thres := a.Threshold(ca.Len())

	errs := sender.Send(req, iter2slice(ca)...)

	go a.waitResp(errs, ca.Len()-thres, cancel)

	go a.waitCtx(innerCtx, ctx, cancel)

	count := 0
	signature := &Signature{}
	for count < thres {
		addr, resp, err := rcvr.Recv(innerCtx)
		if err != nil {
			return nil, xerrors.Errorf("couldn't receive more messages: %v", err)
		}

		pubkey, index := ca.GetPublicKey(addr)
		if index >= 0 {
			err = a.merge(signature, resp, index, pubkey, digest)
			if err != nil {
				dela.Logger.Warn().Err(err).Send()
			} else {
				count++
			}
		}
	}

	// Each signature is individually verified so we can assume the aggregated
	// signature is correct.
	return signature, nil
}

func (a thresholdActor) waitResp(errs <-chan error, maxErrs int, cancel func()) {
	errCount := 0
	for err := range errs {
		dela.Logger.Warn().Err(err).Send()
		errCount++

		if errCount > maxErrs {
			dela.Logger.Warn().Msg("aborting collective signing due to too many errors")
			cancel()
			return
		}
	}
}

func (a thresholdActor) waitCtx(inner, upper context.Context, cancel func()) {
	for {
		select {
		case <-upper.Done():
			// Upper context has been canceled so the inner should be
			// aborted.
			cancel()
			return
		case <-inner.Done():
			return
		}
	}
}

func (a thresholdActor) merge(signature *Signature, resp proto.Message,
	index int, pubkey crypto.PublicKey, digest []byte) error {

	sig, err := a.signer.GetSignatureFactory().FromProto(resp)
	if err != nil {
		return xerrors.Errorf("couldn't decode signature: %v", err)
	}

	err = pubkey.Verify(digest, sig)
	if err != nil {
		return xerrors.Errorf("couldn't verify: %v", err)
	}

	err = signature.Merge(a.signer, index, sig)
	if err != nil {
		return xerrors.Errorf("couldn't merge signature: %v", err)
	}

	return nil
}

func iter2slice(players mino.Players) []mino.Address {
	addrs := make([]mino.Address, 0, players.Len())
	iter := players.AddressIterator()
	for iter.HasNext() {
		addrs = append(addrs, iter.GetNext())
	}

	return addrs
}
