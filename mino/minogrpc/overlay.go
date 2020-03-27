package minogrpc

import (
	context "context"
	"crypto/tls"

	"github.com/golang/protobuf/ptypes"
	"go.dedis.ch/fabric"
	"go.dedis.ch/fabric/encoding"
	"go.dedis.ch/fabric/mino"
	"golang.org/x/xerrors"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
)

// gRPC service for the overlay. The handler map points to the one in
// Server.Handlers, which is updated each time the makeRPC function is called.
type overlayService struct {
	handlers    map[string]mino.Handler
	addr        address
	neighbours  map[string]Peer
	srvCert     *tls.Certificate
	traffic     *traffic
	handlerRcvr map[string]receiver
}

// Call is the implementation of the overlay.Call proto definition
func (o overlayService) Call(ctx context.Context, msg *OverlayMsg) (*OverlayMsg, error) {
	// We fetch the uri that identifies the handler in the handlers map with the
	// grpc metadata api. Using context.Value won't work.
	headers, ok := metadata.FromIncomingContext(ctx)
	if !ok {
		return nil, xerrors.Errorf("header not found in provided context")
	}

	apiURI, ok := headers[headerURIKey]
	if !ok {
		return nil, xerrors.Errorf("%s not found in context header", headerURIKey)
	}
	if len(apiURI) != 1 {
		return nil, xerrors.Errorf("unexpected number of elements in %s "+
			"header. Expected 1, found %d", headerURIKey, len(apiURI))
	}

	handler, ok := o.handlers[apiURI[0]]
	if !ok {
		return nil, xerrors.Errorf("didn't find the '%s' handler in the map "+
			"of handlers, did you register it?", apiURI[0])
	}

	var dynamicAny ptypes.DynamicAny
	err := ptypes.UnmarshalAny(msg.Message, &dynamicAny)
	if err != nil {
		return nil, encoding.NewAnyDecodingError(msg.Message, err)
	}

	req := mino.Request{
		Address: o.addr,
		Message: dynamicAny.Message,
	}

	result, err := handler.Process(req)
	if err != nil {
		return nil, xerrors.Errorf("failed to call the Process function from "+
			"the handler using the provided message: %v", err)
	}

	anyResult, err := ptypes.MarshalAny(result)
	if err != nil {
		return nil, encoding.NewAnyEncodingError(result, err)
	}

	return &OverlayMsg{Message: anyResult}, nil
}

// Stream is the fonction used to perform mino.RPC.Stream() calls. It is called
// by the client side.
func (o overlayService) Stream(stream Overlay_StreamServer) error {
	// We fetch the uri that identifies the handler in the handlers map with the
	// grpc metadata api. Using context.Value won't work.
	ctx := stream.Context()
	headers, ok := metadata.FromIncomingContext(ctx)
	if !ok {
		return xerrors.Errorf("header not found in provided context")
	}

	apiURI, ok := headers[headerURIKey]
	if !ok {
		return xerrors.Errorf("%s not found in context header", headerURIKey)
	}
	if len(apiURI) != 1 {
		return xerrors.Errorf("unexpected number of elements in apiuri "+
			"header. Expected 1, found %d", len(apiURI))
	}

	rcvr, ok := o.handlerRcvr[apiURI[0]]
	if ok {
		go func() {
			for {
				msg, err := stream.Recv()
				status, ok := status.FromError(err)
				if ok && err != nil && status.Code() == codes.Canceled {
					return
				}
				if err != nil {
					fabric.Logger.Error().Msgf("failed to receive in overlay: %v", err)
					rcvr.errs <- xerrors.Errorf("failed to receive in overlay: %v", err)
				}
				rcvr.in <- msg
			}
		}()
		<-o.handlerRcvr[apiURI[0]].stop
		return nil
	}

	handler, ok := o.handlers[apiURI[0]]
	if !ok {
		return xerrors.Errorf("didn't find the '%s' handler in the map "+
			"of handlers, did you register it?", apiURI[0])
	}

	// This participant is used to send back messages that must be
	// relayed.
	// o.participants["server_"+o.addr.String()] = stream

	// For the moment this sender can only receive messages to itself
	// TODO: find a way to know the other nodes.
	sender := &sender{
		// This address is used when the client doesn't find the address it
		// should send the message to in the list of participant. In that case
		// it packs the message in an enveloppe and send it back to this
		// address, which is registered in the list of participant.
		address:      o.addr,
		participants: map[string]overlayStream{o.addr.String(): stream},
		name:         "remote RPC",
		neighbours:   o.neighbours,
		srvCert:      o.srvCert,
		traffic:      o.traffic,
	}

	receiver := receiver{
		in:      make(chan *OverlayMsg),
		errs:    make(chan error),
		name:    "remote RPC",
		stop:    make(chan interface{}),
		traffic: o.traffic,
	}
	go func() {
		for {
			msg, err := stream.Recv()
			status, ok := status.FromError(err)
			if ok && err != nil && status.Code() == codes.Canceled {
				close(receiver.in)
				return
			}
			if err != nil {
				fabric.Logger.Error().Msgf("failed to receive in overlay: %v", err)
				receiver.errs <- xerrors.Errorf("failed to receive in overlay: %v", err)
			}
			receiver.in <- msg
		}
	}()
	o.handlerRcvr[apiURI[0]] = receiver
	err := handler.Stream(sender, receiver)
	if err != nil {
		return xerrors.Errorf("failed to call the stream handler: %v", err)
	}
	close(receiver.stop)
	return nil

}
