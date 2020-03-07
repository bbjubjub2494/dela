package minoch

import (
	"context"

	"github.com/golang/protobuf/proto"
	"github.com/golang/protobuf/ptypes"
	"github.com/golang/protobuf/ptypes/any"
	"go.dedis.ch/fabric/mino"
	"golang.org/x/xerrors"
)

// Envelope is the wrapper to send messages through streams.
type Envelope struct {
	to      []address
	from    address
	message *any.Any
}

// RPC is an implementation of the mino.RPC interface.
type RPC struct {
	manager *Manager
	path    string
	h       mino.Handler
}

// Call sends the message to all participants and gather their reply.
func (c RPC) Call(req proto.Message, nodes ...mino.Node) (<-chan proto.Message, <-chan error) {
	out := make(chan proto.Message, len(nodes))
	errs := make(chan error, len(nodes))

	go func() {
		for _, node := range nodes {
			peer := c.manager.get(node.GetAddress().String())
			if peer != nil {
				resp, err := peer.rpcs[c.path].h.Process(req)
				if err != nil {
					errs <- err
				}

				if resp != nil {
					out <- resp
				}
			}
		}

		close(out)
	}()

	return out, errs
}

// Stream opens a stream. The caller is responsible for cancelling the context
// to close the stream.
func (c RPC) Stream(ctx context.Context, nodes ...mino.Node) (mino.Sender, mino.Receiver) {
	in := make(chan Envelope)
	out := make(chan Envelope, 1)
	errs := make(chan error, 1)

	outs := make(map[string]receiver)

	for _, node := range nodes {
		ch := make(chan Envelope, 1)
		outs[node.GetAddress().String()] = receiver{out: ch}

		peer := c.manager.instances[node.GetAddress().String()]

		go func(r receiver) {
			s := sender{
				addr: peer.GetAddress(),
				in:   in,
			}

			err := peer.rpcs[c.path].h.Stream(s, r)
			if err != nil {
				errs <- err
			}
		}(outs[node.GetAddress().String()])
	}

	orchSender := sender{addr: address{}, in: in}
	orchRecv := receiver{out: out, errs: errs}

	go func() {
		for {
			select {
			case <-ctx.Done():
				// closes the orchestrator..
				close(out)
				// closes the participants..
				for _, r := range outs {
					close(r.out)
				}
				return
			case env := <-in:
				for _, to := range env.to {
					if to.String() == "" {
						orchRecv.out <- env
					} else {
						outs[to.String()].out <- env
					}
				}
			}
		}
	}()

	return orchSender, orchRecv
}

type sender struct {
	addr mino.Address
	in   chan Envelope
}

func (s sender) Send(msg proto.Message, nodes ...mino.Node) error {
	a, err := ptypes.MarshalAny(msg)
	if err != nil {
		return err
	}

	addrs := make([]address, len(nodes))
	for i, node := range nodes {
		addrs[i] = node.GetAddress().(address)
	}

	go func() {
		s.in <- Envelope{
			from:    s.addr.(address),
			to:      addrs,
			message: a,
		}
	}()

	return nil
}

type receiver struct {
	out  chan Envelope
	errs chan error
}

func (r receiver) Recv(ctx context.Context) (mino.Address, proto.Message, error) {
	select {
	case env := <-r.out:
		var da ptypes.DynamicAny
		err := ptypes.UnmarshalAny(env.message, &da)
		if err != nil {
			return nil, nil, err
		}

		return env.from, da.Message, nil
	case err := <-r.errs:
		return nil, nil, err
	case <-ctx.Done():
		return nil, nil, xerrors.New("timeout")
	}
}
