// Package skipchain implements the blockchain interface by using the skipchain
// design, e.i. blocks are linked by one or several forward links collectively
// signed by the participants.
//
// TODO: think about versioning for upgradability.
package skipchain

import (
	"context"
	"fmt"
	"time"

	"github.com/golang/protobuf/proto"
	"github.com/rs/zerolog"
	"go.dedis.ch/fabric"
	"go.dedis.ch/fabric/blockchain"
	"go.dedis.ch/fabric/consensus"
	"go.dedis.ch/fabric/crypto"
	"go.dedis.ch/fabric/encoding"
	"go.dedis.ch/fabric/mino"
	"golang.org/x/xerrors"
)

//go:generate protoc -I ./ --go_out=./ ./messages.proto

const (
	// defaultPropagationTimeout is the default maximum amount of time given to
	// a propagation to reach every player.
	defaultPropogationTimeout = 30 * time.Second
)

// Skipchain is a blockchain that is using collective signatures to create links
// between the blocks.
//
// - implements blockchain.Blockchain
// - implements fmt.Stringer
type Skipchain struct {
	logger    zerolog.Logger
	mino      mino.Mino
	db        Database
	consensus consensus.Consensus
	watcher   blockchain.Observable
	encoder   encoding.ProtoMarshaler
}

// NewSkipchain returns a new instance of Skipchain.
func NewSkipchain(m mino.Mino, consensus consensus.Consensus) *Skipchain {
	db := NewInMemoryDatabase()

	return &Skipchain{
		logger:    fabric.Logger,
		mino:      m,
		db:        db,
		consensus: consensus,
		watcher:   blockchain.NewWatcher(),
		encoder:   encoding.NewProtoEncoder(),
	}
}

// Listen implements blockchain.Blockchain. It registers the RPC and starts the
// consensus module.
func (s *Skipchain) Listen(proc blockchain.PayloadProcessor) (blockchain.Actor, error) {
	actor := skipchainActor{
		Skipchain:   s,
		hashFactory: sha256Factory{},
		rand:        crypto.CryptographicRandomGenerator{},
	}

	var err error
	actor.rpc, err = s.mino.MakeRPC("skipchain", newHandler(s, proc))
	if err != nil {
		return nil, xerrors.Errorf("couldn't create the rpc: %v", err)
	}

	actor.consensus, err = s.consensus.Listen(newBlockValidator(s, proc, s.watcher))
	if err != nil {
		return nil, xerrors.Errorf("couldn't start the consensus: %v", err)
	}

	return actor, nil
}

// GetBlockFactory implements blockchain.Blockchain. It returns the block
// factory for skipchains.
func (s *Skipchain) GetBlockFactory() blockchain.BlockFactory {
	return blockFactory{
		Skipchain:   s,
		encoder:     s.encoder,
		hashFactory: sha256Factory{},
	}
}

// GetBlock implements blockchain.Blockchain. It returns the latest block.
func (s *Skipchain) GetBlock() (blockchain.Block, error) {
	block, err := s.db.ReadLast()
	if err != nil {
		return nil, xerrors.Errorf("couldn't read the latest block: %v", err)
	}

	return block, nil
}

// GetVerifiableBlock implements blockchain.Blockchain. It reads the latest
// block of the chain and creates a verifiable proof of the shortest chain from
// the genesis to the block.
func (s *Skipchain) GetVerifiableBlock() (blockchain.VerifiableBlock, error) {
	block, err := s.db.ReadLast()
	if err != nil {
		return nil, xerrors.Errorf("couldn't read the latest block: %v", err)
	}

	chain, err := s.consensus.GetChain(block.GetHash())
	if err != nil {
		return nil, xerrors.Errorf("couldn't read the chain: %v", err)
	}

	vb := VerifiableBlock{
		SkipBlock: block,
		Chain:     chain,
	}

	return vb, nil
}

// Watch implements blockchain.Blockchain. It registers the observer so that it
// will be notified of new blocks. The caller is responsible for cancelling the
// context when the work is done.
func (s *Skipchain) Watch(ctx context.Context) <-chan blockchain.Block {
	ch := make(chan blockchain.Block, 10)
	obs := skipchainObserver{ch: ch}

	s.watcher.Add(obs)

	// Go routine to listen to the context cancel event. When it occurs, the
	// observer will be removed.
	go func() {
		<-ctx.Done()
		s.watcher.Remove(obs)
		close(ch)
	}()

	return ch
}

// String implements fmt.Stringer. It returns a simple representation of the
// skipchain instance to easily identify it.
func (s *Skipchain) String() string {
	return fmt.Sprintf("skipchain@%v", s.mino.GetAddress())
}

// skipchainActor provides the primitives of a blockchain actor.
//
// - implements blockchain.Actor
type skipchainActor struct {
	*Skipchain
	hashFactory crypto.HashFactory
	rand        crypto.RandGenerator
	consensus   consensus.Actor
	rpc         mino.RPC
}

// InitChain implements blockchain.Actor. It creates a genesis block if none
// exists and propagate it to the conodes.
func (a skipchainActor) InitChain(data proto.Message, players mino.Players) error {
	_, err := a.db.Read(0)
	if err == nil {
		// Genesis block already exists.
		return nil
	}

	if !xerrors.Is(err, NewNoBlockError(0)) {
		return xerrors.Errorf("couldn't read the genesis block: %v", err)
	}

	iter := players.AddressIterator()

	if iter.HasNext() && iter.GetNext().Equal(a.mino.GetAddress()) {
		// Only the first player tries to create the genesis block and then
		// propagates it to the other players.
		// This is done only once for a new chain thus we can assume that the
		// first one will be online at that moment.
		err := a.newChain(data, players)
		if err != nil {
			return xerrors.Errorf("couldn't init genesis block: %w", err)
		}
	}

	return nil
}

func (a skipchainActor) newChain(data proto.Message, conodes mino.Players) error {
	randomBackLink := Digest{}
	n, err := a.rand.Read(randomBackLink[:])
	if err != nil {
		return xerrors.Errorf("couldn't generate backlink: %v", err)
	}
	if n != len(randomBackLink) {
		return xerrors.Errorf("mismatch rand length %d != %d", n, len(randomBackLink))
	}

	genesis := SkipBlock{
		Index:     0,
		GenesisID: Digest{},
		BackLink:  randomBackLink,
		Payload:   data,
	}

	err = a.GetBlockFactory().(blockFactory).prepareBlock(&genesis)
	if err != nil {
		return xerrors.Errorf("couldn't create block: %v", err)
	}

	packed, err := a.encoder.Pack(genesis)
	if err != nil {
		return xerrors.Errorf("couldn't pack genesis: %v", err)
	}

	msg := &PropagateGenesis{
		Genesis: packed.(*BlockProto),
	}

	ctx, cancel := context.WithTimeout(context.Background(), defaultPropogationTimeout)
	defer cancel()

	closing, errs := a.rpc.Call(ctx, msg, conodes)
	select {
	case <-closing:
		return nil
	case err := <-errs:
		return xerrors.Errorf("couldn't propagate: %v", err)
	}
}

// Store implements blockchain.Actor. It will append a new block to chain filled
// with the data.
func (a skipchainActor) Store(data proto.Message, players mino.Players) error {
	factory := a.GetBlockFactory().(blockFactory)

	previous, err := a.db.ReadLast()
	if err != nil {
		return xerrors.Errorf("couldn't read the latest block: %v", err)
	}

	block, err := factory.fromPrevious(previous, data)
	if err != nil {
		return xerrors.Errorf("couldn't create next block: %v", err)
	}

	err = a.consensus.Propose(block)
	if err != nil {
		return xerrors.Errorf("couldn't propose the block: %v", err)
	}

	return nil
}

// skipchainObserver can be registered in the watcher to listen for incoming new
// blocks.
//
// - implements blockchain.Observer
type skipchainObserver struct {
	ch chan blockchain.Block
}

// NotifyCallback implements blockchain.Observer. It sends the event to the
// channel if the type is correct, otherwise it issues a warning.
func (o skipchainObserver) NotifyCallback(event interface{}) {
	block, ok := event.(SkipBlock)
	if !ok {
		fabric.Logger.Warn().Msgf("got invalid event '%T'", event)
		return
	}

	o.ch <- block
}
