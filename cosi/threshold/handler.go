package threshold

import (
	"context"
	"io"

	"go.dedis.ch/dela"
	"go.dedis.ch/dela/cosi"
	"go.dedis.ch/dela/mino"
	"golang.org/x/xerrors"
)

// thresholdHandler is an implementation of mino.RPC for a threshold collective
// signing.
type thresholdHandler struct {
	*CoSi
	mino.UnsupportedHandler

	reactor cosi.Reactor
}

func newHandler(c *CoSi, hasher cosi.Reactor) thresholdHandler {
	return thresholdHandler{
		CoSi:    c,
		reactor: hasher,
	}
}

// Stream implements mino.RPC. It listens for incoming messages and tries to
// send back the signature. If the message is malformed, it is ignored.
func (h thresholdHandler) Stream(out mino.Sender, in mino.Receiver) error {
	for {
		err := h.processRequest(out, in)
		if err == io.EOF {
			return nil
		}
		if err != nil {
			dela.Logger.Warn().Err(err).Send()
		}
	}
}

func (h thresholdHandler) processRequest(sender mino.Sender, rcvr mino.Receiver) error {
	ctx := context.Background()

	addr, msg, err := rcvr.Recv(ctx)
	if err == io.EOF {
		return err
	}
	if err != nil {
		return xerrors.Errorf("failed to receive: %v", err)
	}

	req, ok := msg.(cosi.SignatureRequest)
	if !ok {
		return xerrors.Errorf("invalid request type '%T'", msg)
	}

	buffer, err := h.reactor.Invoke(addr, req.Value)
	if err != nil {
		return xerrors.Errorf("couldn't hash message: %v", err)
	}

	signature, err := h.signer.Sign(buffer)
	if err != nil {
		return xerrors.Errorf("couldn't sign: %v", err)
	}

	resp := cosi.SignatureResponse{
		Signature: signature,
	}

	err = <-sender.Send(resp, addr)
	if err != nil {
		return xerrors.Errorf("couldn't send the response: %v", err)
	}

	return nil
}
