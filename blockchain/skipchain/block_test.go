package skipchain

import (
	"bytes"
	"encoding/binary"
	fmt "fmt"
	"hash"
	"math/rand"
	"reflect"
	"testing"
	"testing/quick"

	proto "github.com/golang/protobuf/proto"
	"github.com/golang/protobuf/ptypes"
	any "github.com/golang/protobuf/ptypes/any"
	"github.com/golang/protobuf/ptypes/empty"
	"github.com/golang/protobuf/ptypes/wrappers"
	"github.com/stretchr/testify/require"
	"go.dedis.ch/fabric/consensus"
	"go.dedis.ch/fabric/cosi"
	"go.dedis.ch/fabric/crypto"
	"go.dedis.ch/fabric/encoding"
	"go.dedis.ch/fabric/mino"
	"golang.org/x/xerrors"
)

func TestDigest_Bytes(t *testing.T) {
	f := func(buffer [32]byte) bool {
		id := Digest(buffer)

		return bytes.Equal(id.Bytes(), buffer[:])
	}

	err := quick.Check(f, &quick.Config{})
	require.NoError(t, err)
}

func TestDigest_String(t *testing.T) {
	f := func(buffer [32]byte) bool {
		id := Digest(buffer)

		return id.String() == fmt.Sprintf("%x", buffer)[:16]
	}

	err := quick.Check(f, nil)
	require.NoError(t, err)
}

func TestSkipBlock_GetHash(t *testing.T) {
	f := func(block SkipBlock) bool {
		return bytes.Equal(block.GetHash(), block.hash.Bytes())
	}

	err := quick.Check(f, nil)
	require.NoError(t, err)
}

func TestSkipBlock_Pack(t *testing.T) {
	f := func(block SkipBlock) bool {
		packed, err := block.Pack()
		if err != nil {
			t.Log(err)
			return false
		}

		pblock := packed.(*BlockProto)

		require.Equal(t, block.Index, pblock.Index)
		require.Equal(t, block.BackLink.Bytes(), pblock.GetBacklink())
		require.Equal(t, block.GenesisID.Bytes(), pblock.GetGenesisID())

		return true
	}

	err := quick.Check(f, nil)
	require.NoError(t, err)
}

func TestSkipBlock_PackFailures(t *testing.T) {
	defer func() { protoenc = encoding.NewProtoEncoder() }()

	block := SkipBlock{
		BackLink: Digest{},
		Payload:  &empty.Empty{},
	}

	e := xerrors.New("pack error")

	protoenc = &testProtoEncoder{err: e}
	_, err := block.Pack()
	require.Error(t, err)
	require.True(t, xerrors.Is(err, e))
	require.True(t, xerrors.Is(err, encoding.NewAnyEncodingError((*empty.Empty)(nil), nil)))
}

func TestSkipBlock_Hash(t *testing.T) {
	block := SkipBlock{
		Conodes: Conodes{randomConode()},
		Payload: &empty.Empty{},
	}

	_, err := block.computeHash(badHashFactory{})
	require.EqualError(t, err, "couldn't write index: oops")

	_, err = block.computeHash(badHashFactory{delay: 1})
	require.Error(t, err)
	require.Contains(t, err.Error(), "couldn't write conodes: ")

	_, err = block.computeHash(badHashFactory{delay: 3})
	require.EqualError(t, err, "couldn't write genesis hash: oops")

	_, err = block.computeHash(badHashFactory{delay: 4})
	require.EqualError(t, err, "couldn't write backlink: oops")

	_, err = block.computeHash(badHashFactory{delay: 5})
	require.EqualError(t, err, "couldn't write payload: oops")
}

func TestSkipBlock_HashUniqueness(t *testing.T) {
	// This test will detect any field added in the SkipBlock structure but
	// not in the hash function. Then it is either added in the hash, or
	// whitelisted in the test. The field should first be set with a value
	// different from the zero of the type.

	block := SkipBlock{
		Index:     1,
		Conodes:   []Conode{randomConode()},
		GenesisID: Digest{1},
		BackLink:  Digest{1},
		Payload:   &wrappers.StringValue{Value: "deadbeef"},
	}

	prevHash, err := block.computeHash(sha256Factory{})
	require.NoError(t, err)

	value := reflect.ValueOf(&block)

	for i := 0; i < value.Elem().NumField(); i++ {
		field := value.Elem().Field(i)

		if !field.CanSet() {
			// ignore private fields.
			continue
		}

		fieldName := value.Elem().Type().Field(i).Name

		field.Set(reflect.Zero(value.Elem().Field(i).Type()))
		newBlock := value.Interface()

		hash, err := newBlock.(*SkipBlock).computeHash(sha256Factory{})
		require.NoError(t, err)

		errMsg := fmt.Sprintf("field %#v produced same hash", fieldName)
		require.NotEqual(t, prevHash, hash, errMsg)

		prevHash = hash
	}
}

func TestSkipBlock_String(t *testing.T) {
	block := SkipBlock{hash: Digest{1}}
	require.Equal(t, block.String(), fmt.Sprintf("Block[0100000000000000]"))
}

func TestVerifiableBlock_Verify(t *testing.T) {
	hash := Digest{1}
	vb := VerifiableBlock{
		SkipBlock: SkipBlock{hash: hash},
		Chain:     fakeChain{hash: hash},
	}

	err := vb.Verify(fakeVerifier{})
	require.NoError(t, err)

	vb.Chain = fakeChain{err: xerrors.New("oops")}
	err = vb.Verify(fakeVerifier{})
	require.EqualError(t, err, "couldn't verify the chain: oops")

	vb.Chain = fakeChain{hash: hash}
	vb.hash = Digest{}
	err = vb.Verify(fakeVerifier{})
	require.Error(t, err)
}

func TestVerifiableBlock_Pack(t *testing.T) {
	f := func(block SkipBlock) bool {
		defer func() { protoenc = encoding.NewProtoEncoder() }()

		vb := VerifiableBlock{
			SkipBlock: block,
			Chain:     fakeChain{},
		}

		packed, err := vb.Pack()
		require.NoError(t, err)
		require.IsType(t, (*VerifiableBlockProto)(nil), packed)

		vb.SkipBlock = SkipBlock{}
		_, err = vb.Pack()
		require.Error(t, err)
		require.True(t, xerrors.Is(err, encoding.NewEncodingError("block", nil)))

		vb.SkipBlock = block
		vb.Chain = fakeChain{err: xerrors.Errorf("oops")}
		_, err = vb.Pack()
		require.Error(t, err)
		require.True(t, xerrors.Is(err, encoding.NewEncodingError("chain", nil)))

		vb.Chain = fakeChain{}
		protoenc = &testProtoEncoder{delay: 1, err: xerrors.New("oops")}
		_, err = vb.Pack()
		require.Error(t, err)
		require.True(t, xerrors.Is(err, encoding.NewAnyEncodingError((*empty.Empty)(nil), nil)))

		return true
	}

	err := quick.Check(f, nil)
	require.NoError(t, err)
}

func TestBlockFactory_FromPrevious(t *testing.T) {
	f := func(prev SkipBlock) bool {
		factory := blockFactory{
			hashFactory: sha256Factory{},
		}

		block, err := factory.fromPrevious(prev, &empty.Empty{})
		require.NoError(t, err)
		require.Equal(t, prev.Index+1, block.Index)
		require.Equal(t, prev.GenesisID, block.GenesisID)
		require.Equal(t, prev.GetHash(), block.BackLink.Bytes())

		factory.hashFactory = badHashFactory{}
		_, err = factory.fromPrevious(prev, nil)
		require.Error(t, err)
		require.Contains(t, err.Error(), "couldn't make block: ")

		return true
	}

	err := quick.Check(f, nil)
	require.NoError(t, err)
}

func TestBlockFactory_DecodeConodes(t *testing.T) {
	pb := []*ConodeProto{{}, {}, {}}

	factory := blockFactory{
		Skipchain: &Skipchain{
			cosi: fakeCosi{},
			mino: fakeMino{},
		},
	}

	conodes, err := factory.decodeConodes(pb)
	require.NoError(t, err)
	require.Len(t, conodes, 3)

	factory.cosi = fakeCosi{err: xerrors.New("oops")}
	_, err = factory.decodeConodes(pb)
	require.Error(t, err)
	require.True(t, xerrors.Is(err, encoding.NewDecodingError("public key", nil)))
}

func TestBlockFactory_DecodeBlock(t *testing.T) {
	f := func(block SkipBlock) bool {
		factory := blockFactory{
			hashFactory: sha256Factory{},
			Skipchain: &Skipchain{
				cosi: fakeCosi{},
				mino: fakeMino{},
			},
		}

		packed, err := block.Pack()
		require.NoError(t, err)

		newBlock, err := factory.decodeBlock(packed.(*BlockProto))
		require.NoError(t, err)
		require.Equal(t, block, newBlock)

		_, err = factory.decodeBlock(&empty.Empty{})
		require.EqualError(t, err, "invalid message type '*empty.Empty'")

		_, err = factory.decodeBlock(&BlockProto{})
		require.Error(t, err)
		require.True(t, xerrors.Is(err,
			encoding.NewAnyDecodingError((*ptypes.DynamicAny)(nil), nil)))

		factory.cosi = fakeCosi{err: xerrors.New("oops")}
		_, err = factory.decodeBlock(packed.(*BlockProto))
		require.EqualError(t, err, "couldn't make verifier: oops")

		factory.cosi = fakeCosi{}
		factory.hashFactory = badHashFactory{}
		_, err = factory.decodeBlock(packed.(*BlockProto))
		require.Error(t, err)
		require.Contains(t, err.Error(), "couldn't make block: ")

		return true
	}

	err := quick.Check(f, nil)
	require.NoError(t, err)
}

func TestBlockFactory_FromVerifiable(t *testing.T) {
	f := func(block SkipBlock) bool {
		factory := blockFactory{
			hashFactory: sha256Factory{},
			Skipchain: &Skipchain{
				cosi:      fakeCosi{},
				mino:      fakeMino{},
				consensus: fakeConsensus{hash: block.hash},
			},
		}

		packed, err := block.Pack()
		require.NoError(t, err)

		pb := &VerifiableBlockProto{
			Block: packed.(*BlockProto),
			Chain: &any.Any{},
		}

		b, err := factory.FromVerifiable(pb)
		require.NoError(t, err)
		require.NotNil(t, b)

		_, err = factory.FromVerifiable(&empty.Empty{})
		require.EqualError(t, err, "invalid message type '*empty.Empty'")

		factory.hashFactory = badHashFactory{}
		_, err = factory.FromVerifiable(pb)
		require.Error(t, err)
		require.Contains(t, err.Error(), "couldn't decode the block: ")

		factory.hashFactory = sha256Factory{}
		factory.consensus = fakeConsensus{err: xerrors.New("oops")}
		_, err = factory.FromVerifiable(pb)
		require.EqualError(t, err, "couldn't decode the chain: oops")

		factory.consensus = fakeConsensus{errChain: xerrors.New("oops")}
		_, err = factory.FromVerifiable(pb)
		require.EqualError(t, err,
			"couldn't verify: couldn't verify the chain: oops")

		return true
	}

	err := quick.Check(f, nil)
	require.NoError(t, err)
}

// -----------------
// Utility functions

func randomUint64(rand *rand.Rand) uint64 {
	buffer := make([]byte, 16)
	rand.Read(buffer)
	return binary.LittleEndian.Uint64(buffer)
}

func randomUint32(rand *rand.Rand) uint32 {
	buffer := make([]byte, 8)
	rand.Read(buffer)
	return binary.LittleEndian.Uint32(buffer)
}

func randomConode() Conode {
	buffer := make([]byte, 4)
	rand.Read(buffer)
	return Conode{
		addr:      fakeAddress{id: buffer},
		publicKey: fakePublicKey{},
	}
}

func (s SkipBlock) Generate(rand *rand.Rand, size int) reflect.Value {
	genesisID := Digest{}
	rand.Read(genesisID[:])

	dataHash := make([]byte, size)
	rand.Read(dataHash)

	backLink := Digest{}
	rand.Read(backLink[:])

	block := SkipBlock{
		verifier:  fakeVerifier{},
		Index:     randomUint64(rand),
		Conodes:   Conodes{},
		GenesisID: genesisID,
		BackLink:  backLink,
		Payload:   &empty.Empty{},
	}

	hash, _ := block.computeHash(sha256Factory{})
	block.hash = hash

	return reflect.ValueOf(block)
}

type fakeAddress struct {
	id  []byte
	err error
}

func (a fakeAddress) Equal(other mino.Address) bool {
	return bytes.Equal(other.(fakeAddress).id, a.id)
}

func (a fakeAddress) MarshalText() ([]byte, error) {
	return []byte(a.id), a.err
}

func (a fakeAddress) String() string {
	return fmt.Sprintf("%x", a.id)
}

type fakePublicKey struct {
	crypto.PublicKey
	err error
}

func (pk fakePublicKey) MarshalBinary() ([]byte, error) {
	return []byte{}, pk.err
}

func (pk fakePublicKey) Pack() (proto.Message, error) {
	return &empty.Empty{}, pk.err
}

type testProtoEncoder struct {
	encoding.ProtoEncoder
	delay int
	err   error
}

func (e *testProtoEncoder) Marshal(pb proto.Message) ([]byte, error) {
	if e.err != nil {
		if e.delay == 0 {
			return nil, e.err
		}
		e.delay--
	}

	return proto.Marshal(pb)
}

func (e *testProtoEncoder) MarshalAny(pb proto.Message) (*any.Any, error) {
	if e.err != nil {
		if e.delay == 0 {
			return nil, e.err
		}
		e.delay--
	}

	return ptypes.MarshalAny(pb)
}

func (e *testProtoEncoder) UnmarshalAny(any *any.Any, pb proto.Message) error {
	if e.err != nil {
		if e.delay == 0 {
			return e.err
		}
		e.delay--
	}

	return ptypes.UnmarshalAny(any, pb)
}

type testSignature struct {
	crypto.Signature
	buffer []byte
	err    error
}

func (s testSignature) MarshalBinary() ([]byte, error) {
	return s.buffer, s.err
}

func (s testSignature) Pack() (proto.Message, error) {
	return &empty.Empty{}, s.err
}

type testSignatureFactory struct {
	err error
}

func (f testSignatureFactory) FromProto(pb proto.Message) (crypto.Signature, error) {
	return testSignature{}, f.err
}

type testVerifier struct {
	err   error
	delay int
	calls []struct {
		msg []byte
		sig crypto.Signature
	}

	crypto.Verifier
}

func (v *testVerifier) GetSignatureFactory() crypto.SignatureFactory {
	return testSignatureFactory{err: v.err}
}

func (v *testVerifier) Verify(msg []byte, sig crypto.Signature) error {
	v.calls = append(v.calls, struct {
		msg []byte
		sig crypto.Signature
	}{msg, sig})

	if v.err != nil {
		if v.delay == 0 {
			return v.err
		}
		v.delay--
	}

	return nil
}

type badHash struct {
	hash.Hash
	delay int
}

func (h *badHash) Write([]byte) (int, error) {
	if h.delay > 0 {
		h.delay--
		return 0, nil
	}
	return 0, xerrors.New("oops")
}

type badHashFactory struct {
	delay int
}

func (f badHashFactory) New() hash.Hash {
	return &badHash{delay: f.delay}
}

type fakeVerifier struct {
	crypto.Verifier
}

func (v fakeVerifier) GetPublicKeyFactory() crypto.PublicKeyFactory {
	return nil
}

type fakeCosi struct {
	cosi.CollectiveSigning
	err error
}

func (cosi fakeCosi) GetPublicKeyFactory() crypto.PublicKeyFactory {
	return fakePublicKeyFactory{err: cosi.err}
}

func (cosi fakeCosi) GetVerifier(cosi.CollectiveAuthority) (crypto.Verifier, error) {
	return fakeVerifier{}, cosi.err
}

type fakeAddressFactory struct {
	mino.AddressFactory
}

func (f fakeAddressFactory) FromText([]byte) mino.Address {
	return nil
}

type fakeMino struct {
	mino.Mino
	err error
}

func (m fakeMino) GetAddress() mino.Address {
	return fakeAddress{id: []byte{0xaa}}
}

func (m fakeMino) GetAddressFactory() mino.AddressFactory {
	return fakeAddressFactory{}
}

func (m fakeMino) MakeRPC(name string, h mino.Handler) (mino.RPC, error) {
	return nil, m.err
}

type fakePublicKeyFactory struct {
	crypto.PublicKeyFactory
	err error
}

func (f fakePublicKeyFactory) FromProto(pb proto.Message) (crypto.PublicKey, error) {
	return nil, f.err
}

type fakeChain struct {
	consensus.Chain
	hash Digest
	err  error
}

func (c fakeChain) Verify(crypto.Verifier) error {
	return c.err
}

func (c fakeChain) GetLastHash() []byte {
	return c.hash.Bytes()
}

func (c fakeChain) Pack() (proto.Message, error) {
	return &empty.Empty{}, c.err
}

type fakeChainFactory struct {
	consensus.ChainFactory
	hash     Digest
	err      error
	errChain error
}

func (f fakeChainFactory) FromProto(proto.Message) (consensus.Chain, error) {
	return fakeChain{hash: f.hash, err: f.errChain}, f.err
}

type fakeConsensus struct {
	consensus.Consensus
	hash     Digest
	err      error
	errChain error
}

func (c fakeConsensus) GetChainFactory() consensus.ChainFactory {
	return fakeChainFactory{
		hash:     c.hash,
		err:      c.err,
		errChain: c.errChain,
	}
}

func (c fakeConsensus) GetChain(id []byte) (consensus.Chain, error) {
	return fakeChain{}, c.err
}

func (c fakeConsensus) Listen(consensus.Validator) (consensus.Actor, error) {
	return nil, c.err
}
