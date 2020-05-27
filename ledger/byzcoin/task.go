package byzcoin

import (
	"reflect"

	"github.com/golang/protobuf/proto"
	"github.com/golang/protobuf/ptypes/any"
	"go.dedis.ch/dela/consensus/viewchange"
	"go.dedis.ch/dela/crypto"
	"go.dedis.ch/dela/encoding"
	"go.dedis.ch/dela/ledger/arc/darc"
	"go.dedis.ch/dela/ledger/byzcoin/roster"
	"go.dedis.ch/dela/ledger/inventory"
	"go.dedis.ch/dela/ledger/transactions/basic"
	"go.dedis.ch/dela/mino"
	"golang.org/x/xerrors"
)

// taskFactory is a task factory that can process several types of tasks.
//
// - implements basic.TaskFactory
type taskFactory struct {
	encoder  encoding.ProtoMarshaler
	registry map[reflect.Type]basic.TaskFactory
}

func newtaskFactory(m mino.Mino, signer crypto.Signer,
	i inventory.Inventory) (*taskFactory, viewchange.Governance) {

	f := &taskFactory{
		encoder:  encoding.NewProtoEncoder(),
		registry: make(map[reflect.Type]basic.TaskFactory),
	}

	rosterFactory := roster.NewRosterFactory(m.GetAddressFactory(), signer.GetPublicKeyFactory())
	gov := roster.NewTaskManager(rosterFactory, i)

	f.Register((*darc.Task)(nil), darc.NewTaskFactory())
	f.Register((*roster.Task)(nil), gov)

	return f, gov
}

// Register registers the factory for the protobuf message. If a message has
// already been registered, it will overwritten.
func (f *taskFactory) Register(pb proto.Message, factory basic.TaskFactory) {
	key := reflect.TypeOf(pb)
	f.registry[key] = factory
}

// FromProto implements basic.TaskFactory. It returns the server task for the
// protobuf message if appropriate, otherwise an error.
func (f *taskFactory) FromProto(in proto.Message) (basic.ServerTask, error) {
	inAny, ok := in.(*any.Any)
	if ok {
		var err error
		in, err = f.encoder.UnmarshalDynamicAny(inAny)
		if err != nil {
			return nil, xerrors.Errorf("couldn't unmarshal message: %v", err)
		}
	}

	key := reflect.TypeOf(in)
	factory := f.registry[key]
	if factory == nil {
		return nil, xerrors.Errorf("unknown task type '%T'", in)
	}

	task, err := factory.FromProto(in)
	if err != nil {
		return nil, xerrors.Errorf("couldn't decode task: %v", err)
	}

	return task, nil
}
