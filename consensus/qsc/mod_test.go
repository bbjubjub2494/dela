package qsc

import (
	"context"
	"crypto/rand"
	"fmt"
	"sync"
	"testing"

	"github.com/golang/protobuf/proto"
	"github.com/stretchr/testify/require"
	"go.dedis.ch/fabric/consensus"
	"go.dedis.ch/fabric/encoding"
	internal "go.dedis.ch/fabric/internal/testing"
	"go.dedis.ch/fabric/mino/minoch"
	"golang.org/x/xerrors"
)

func TestMessages(t *testing.T) {
	messages := []proto.Message{
		&Message{},
		&MessageSet{},
		&View{},
		&RequestMessageSet{},
		&Epoch{},
		&History{},
	}

	for _, m := range messages {
		internal.CoverProtoMessage(t, m)
	}
}

func TestQSC_Basic(t *testing.T) {
	n := 5
	k := 100

	val := &fakeValidator{}
	val.wg.Add(n * k)

	cons := makeQSC(t, n)
	actors := make([]consensus.Actor, n)
	for i, c := range cons {
		actor, err := c.Listen(val)
		require.NoError(t, err)

		actors[i] = actor
	}

	for j := 0; j < n; j++ {
		c := cons[j]
		actor := actors[j]
		go func() {
			for i := 0; i < k; i++ {
				err := actor.Propose(newFakeProposal(), nil)
				require.NoError(t, err)
			}
			close(c.ch)
		}()
	}

	val.wg.Wait()

	require.Equal(t, cons[0].history, cons[1].history)
	require.Len(t, cons[0].history, k)
}

func TestQSC_ExecuteRound(t *testing.T) {
	bc := &fakeBroadcast{}
	factory := &fakeFactory{}
	qsc := &Consensus{
		broadcast:        bc,
		historiesFactory: factory,
	}

	bc.err = xerrors.New("oops")
	err := qsc.executeRound(&fakeValidator{})
	require.EqualError(t, err, "couldn't broadcast: oops")

	bc.delay = 1
	factory.err = xerrors.New("oops")
	err = qsc.executeRound(&fakeValidator{})
	require.Error(t, err)
	require.True(t, xerrors.Is(err, encoding.NewDecodingError("broadcasted set", nil)))

	bc.delay = 1
	factory.delay = 1
	err = qsc.executeRound(&fakeValidator{})
	require.EqualError(t, err, "couldn't broadcast: oops")

	bc.err = nil
	factory.delay = 1
	err = qsc.executeRound(&fakeValidator{})
	require.Error(t, err)
	require.True(t, xerrors.Is(err, encoding.NewDecodingError("received set", nil)))

	factory.delay = 2
	err = qsc.executeRound(&fakeValidator{})
	require.Error(t, err)
	require.True(t, xerrors.Is(err, encoding.NewDecodingError("broadcasted set", nil)))

	factory.delay = 3
	err = qsc.executeRound(&fakeValidator{})
	require.Error(t, err)
	require.True(t, xerrors.Is(err, encoding.NewDecodingError("received set", nil)))

	factory.err = nil
	err = qsc.executeRound(badValidator{})
	require.EqualError(t, err, "couldn't commit: oops")
}

// -----------------
// Utility functions

func makeQSC(t *testing.T, n int) []*Consensus {
	manager := minoch.NewManager()
	cons := make([]*Consensus, n)
	players := &fakePlayers{}
	for i := range cons {
		m, err := minoch.NewMinoch(manager, fmt.Sprintf("node%d", i))
		require.NoError(t, err)

		players.addrs = append(players.addrs, m.GetAddress())

		qsc, err := NewQSC(int64(i), m, players)
		require.NoError(t, err)

		cons[i] = qsc
	}

	return cons
}

type fakeValidator struct {
	consensus.Validator
	wg sync.WaitGroup
}

func (v *fakeValidator) Validate(pb proto.Message) (consensus.Proposal, error) {
	return nil, nil
}

func (v *fakeValidator) Commit(id []byte) error {
	v.wg.Done()
	return nil
}

type badValidator struct {
	consensus.Validator
}

func (v badValidator) Commit([]byte) error {
	return xerrors.New("oops")
}

type fakeProposal struct {
	consensus.Proposal
	hash []byte
}

func newFakeProposal() fakeProposal {
	buffer := make([]byte, 32)
	rand.Read(buffer)
	return fakeProposal{hash: buffer}
}

func (p fakeProposal) GetHash() []byte {
	return p.hash
}

type fakeBroadcast struct {
	broadcast
	err   error
	delay int
}

func (b *fakeBroadcast) send(context.Context, history) (*View, error) {
	if b.delay == 0 {
		return nil, b.err
	}
	b.delay--
	return nil, nil
}

type fakeFactory struct {
	historiesFactory
	err   error
	delay int
}

func (f *fakeFactory) FromMessageSet(map[int64]*Message) (histories, error) {
	if f.delay == 0 && f.err != nil {
		return nil, f.err
	}
	f.delay--

	h := history{{random: 1}}
	return histories{h}, nil
}
