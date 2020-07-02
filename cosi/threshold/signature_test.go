package threshold

import (
	"testing"

	"github.com/stretchr/testify/require"
	"go.dedis.ch/dela/internal/testing/fake"
	"go.dedis.ch/dela/mino"
	"go.dedis.ch/dela/serde"
)

func init() {
	RegisterSignatureFormat(fake.GoodFormat, fake.Format{Msg: &Signature{}})
	RegisterSignatureFormat(serde.Format("BAD_TYPE"), fake.Format{Msg: fake.Message{}})
	RegisterSignatureFormat(fake.BadFormat, fake.NewBadFormat())
}

func TestSignature_GetAggregate(t *testing.T) {
	sig := NewSignature(fake.Signature{}, nil)

	require.Equal(t, fake.Signature{}, sig.GetAggregate())
}

func TestSignature_GetMask(t *testing.T) {
	sig := NewSignature(nil, []byte{1})

	require.Equal(t, []byte{1}, sig.GetMask())
}

func TestSignature_HasBit(t *testing.T) {
	sig := &Signature{mask: []byte{0b00000010, 0b10000001}}

	require.True(t, sig.HasBit(1))
	require.True(t, sig.HasBit(8))
	require.True(t, sig.HasBit(15))
	require.False(t, sig.HasBit(16))
	require.False(t, sig.HasBit(-1))
}

func TestSignature_GetIndices(t *testing.T) {
	sig := &Signature{mask: []byte{0x0c, 0x01}}

	require.Equal(t, []int{2, 3, 8}, sig.GetIndices())
}

func TestSignature_Merge(t *testing.T) {
	sig := &Signature{}

	err := sig.Merge(fake.NewSigner(), 2, fake.Signature{})
	require.NoError(t, err)
	require.NotNil(t, sig.agg)

	err = sig.Merge(fake.NewSigner(), 1, fake.Signature{})
	require.NoError(t, err)

	err = sig.Merge(fake.NewSigner(), 1, fake.Signature{})
	require.EqualError(t, err, "index 1 already merged")

	err = sig.Merge(fake.NewBadSigner(), 0, fake.Signature{})
	require.EqualError(t, err, "couldn't aggregate: fake error")
	require.Equal(t, []byte{0b00000110}, sig.mask)
}

func TestSignature_SetBit(t *testing.T) {
	sig := &Signature{}

	sig.setBit(-1)
	require.Nil(t, sig.mask)

	sig.setBit(8)
	require.Len(t, sig.mask, 2)
	require.Equal(t, sig.mask[1], uint8(1))

	sig.setBit(9)
	require.Len(t, sig.mask, 2)
	require.Equal(t, sig.mask[1], uint8(3))
}

func TestSignature_Serialize(t *testing.T) {
	sig := Signature{}

	data, err := sig.Serialize(fake.NewContext())
	require.NoError(t, err)
	require.Equal(t, "fake format", string(data))

	_, err = sig.Serialize(fake.NewBadContext())
	require.EqualError(t, err, "couldn't encode signature: fake error")
}

func TestSignature_MarshalBinary(t *testing.T) {
	sig := &Signature{
		agg:  fake.Signature{},
		mask: []byte{0xff},
	}

	buffer, err := sig.MarshalBinary()
	require.NoError(t, err)
	require.Equal(t, []byte{fake.SignatureByte, 0xff}, buffer)

	sig.agg = fake.NewBadSignature()
	_, err = sig.MarshalBinary()
	require.EqualError(t, err, "couldn't marshal signature: fake error")
}

func TestSignature_Equal(t *testing.T) {
	sig := &Signature{
		agg:  fake.Signature{},
		mask: []byte{0xff},
	}

	require.True(t, sig.Equal(sig))
	require.False(t, sig.Equal(nil))
}

func TestSignatureFactory_Deserialize(t *testing.T) {
	factory := NewSignatureFactory(fake.SignatureFactory{})

	msg, err := factory.Deserialize(fake.NewContext(), nil)
	require.NoError(t, err)
	require.Equal(t, &Signature{}, msg)
}

func TestSignatureFactory_SignatureOf(t *testing.T) {
	factory := NewSignatureFactory(fake.SignatureFactory{})

	sig, err := factory.SignatureOf(fake.NewContext(), nil)
	require.NoError(t, err)
	require.Equal(t, &Signature{}, sig)

	_, err = factory.SignatureOf(fake.NewBadContext(), nil)
	require.EqualError(t, err, "couldn't decode signature: fake error")

	_, err = factory.SignatureOf(fake.NewContextWithFormat(serde.Format("BAD_TYPE")), nil)
	require.EqualError(t, err, "invalid signature of type 'fake.Message'")
}

func TestVerifier_Verify(t *testing.T) {
	call := &fake.Call{}

	verifier := newVerifier(
		fake.NewAuthority(3, fake.NewSigner),
		fake.NewVerifierFactoryWithCalls(call))

	err := verifier.Verify([]byte{0xff}, &Signature{mask: []byte{0x3}})
	require.NoError(t, err)
	require.Equal(t, 1, call.Len())
	require.Equal(t, 2, call.Get(0, 0).(mino.Players).Len())

	err = verifier.Verify([]byte{}, nil)
	require.EqualError(t, err, "invalid signature type '<nil>' != '*threshold.Signature'")

	verifier.factory = fake.NewBadVerifierFactory()
	err = verifier.Verify([]byte{}, &Signature{})
	require.EqualError(t, err, "couldn't make verifier: fake error")

	verifier.factory = fake.NewVerifierFactory(fake.NewBadVerifier())
	err = verifier.Verify([]byte{}, &Signature{})
	require.EqualError(t, err, "invalid signature: fake error")
}
