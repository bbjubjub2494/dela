package roster

import (
	"bytes"
	"testing"

	"github.com/stretchr/testify/require"
	"go.dedis.ch/dela/consensus/viewchange"
	"go.dedis.ch/dela/crypto/bls"
	"go.dedis.ch/dela/internal/testing/fake"
	"go.dedis.ch/dela/mino"
	"go.dedis.ch/dela/serde"
)

func init() {
	RegisterRosterFormat(fake.GoodFormat, fake.Format{Msg: Roster{}})
	RegisterRosterFormat(serde.Format("BAD_TYPE"), fake.Format{Msg: fake.Message{}})
	RegisterRosterFormat(fake.BadFormat, fake.NewBadFormat())
}

func TestIterator_Seek(t *testing.T) {
	roster := FromAuthority(fake.NewAuthority(3, fake.NewSigner))
	iter := &iterator{
		roster: &roster,
	}

	iter.Seek(2)
	require.True(t, iter.HasNext())
	iter.Seek(3)
	require.False(t, iter.HasNext())
}

func TestIterator_HasNext(t *testing.T) {
	iter := &iterator{
		roster: &Roster{addrs: make([]mino.Address, 3)},
	}

	require.True(t, iter.HasNext())

	iter.index = 1
	require.True(t, iter.HasNext())

	iter.index = 2
	require.True(t, iter.HasNext())

	iter.index = 3
	require.False(t, iter.HasNext())

	iter.index = 10
	require.False(t, iter.HasNext())
}

func TestIterator_GetNext(t *testing.T) {
	iter := &iterator{
		roster: &Roster{addrs: make([]mino.Address, 3)},
	}

	for i := 0; i < 3; i++ {
		c := iter.GetNext()
		require.NotNil(t, c)
	}

	require.Equal(t, 3, iter.GetNext())
}

func TestAddressIterator_GetNext(t *testing.T) {
	roster := FromAuthority(fake.NewAuthority(3, fake.NewSigner))
	iter := &addressIterator{
		iterator: &iterator{
			roster: &roster,
		},
	}

	for _, target := range roster.addrs {
		addr := iter.GetNext()
		require.Equal(t, target, addr)
	}

	require.Nil(t, iter.GetNext())
}

func TestPublicKeyIterator_GetNext(t *testing.T) {
	roster := FromAuthority(fake.NewAuthority(3, fake.NewSigner))
	iter := &publicKeyIterator{
		iterator: &iterator{
			roster: &roster,
		},
	}

	for _, target := range roster.pubkeys {
		pubkey := iter.GetNext()
		require.Equal(t, target, pubkey)
	}

	require.Nil(t, iter.GetNext())
}

func TestRoster_Fingerprint(t *testing.T) {
	roster := FromAuthority(fake.NewAuthority(2, fake.NewSigner))

	out := new(bytes.Buffer)
	err := roster.Fingerprint(out)
	require.NoError(t, err)
	require.Equal(t, "\x00\x00\x00\x00PK\x01\x00\x00\x00PK", out.String())

	roster.addrs[0] = fake.NewBadAddress()
	err = roster.Fingerprint(out)
	require.EqualError(t, err, "couldn't marshal address: fake error")

	roster.addrs[0] = fake.NewAddress(0)
	roster.pubkeys[0] = fake.NewBadPublicKey()
	err = roster.Fingerprint(out)
	require.EqualError(t, err, "couldn't marshal public key: fake error")

	roster.pubkeys[0] = fake.PublicKey{}
	err = roster.Fingerprint(fake.NewBadHash())
	require.EqualError(t, err, "couldn't write address: fake error")

	err = roster.Fingerprint(fake.NewBadHashWithDelay(1))
	require.EqualError(t, err, "couldn't write public key: fake error")
}

func TestRoster_Take(t *testing.T) {
	roster := FromAuthority(fake.NewAuthority(3, fake.NewSigner))

	roster2 := roster.Take(mino.RangeFilter(1, 2))
	require.Equal(t, 1, roster2.Len())

	roster2 = roster.Take(mino.RangeFilter(1, 3))
	require.Equal(t, 2, roster2.Len())
}

func TestRoster_Apply(t *testing.T) {
	roster := FromAuthority(fake.NewAuthority(3, fake.NewSigner))
	require.Equal(t, roster, roster.Apply(nil))

	roster2 := roster.Apply(ChangeSet{Remove: []uint32{3, 2, 0}})
	require.Equal(t, roster.Len()-2, roster2.Len())

	roster3 := roster2.Apply(ChangeSet{Add: []Player{{}}})
	require.Equal(t, roster.Len()-1, roster3.Len())
}

func TestRoster_Diff(t *testing.T) {
	roster1 := FromAuthority(fake.NewAuthority(3, fake.NewSigner))

	roster2 := FromAuthority(fake.NewAuthority(4, fake.NewSigner))
	diff := roster1.Diff(roster2).(ChangeSet)
	require.Len(t, diff.Add, 1)

	roster3 := FromAuthority(fake.NewAuthority(2, fake.NewSigner))
	diff = roster1.Diff(roster3).(ChangeSet)
	require.Len(t, diff.Remove, 1)

	roster4 := FromAuthority(fake.NewAuthority(3, fake.NewSigner))
	roster4.addrs[1] = fake.NewAddress(5)
	diff = roster1.Diff(roster4).(ChangeSet)
	require.Equal(t, []uint32{1, 2}, diff.Remove)
	require.Len(t, diff.Add, 2)

	diff = roster1.Diff((viewchange.Authority)(nil)).(ChangeSet)
	require.Equal(t, ChangeSet{}, diff)
}

func TestRoster_Len(t *testing.T) {
	roster := FromAuthority(fake.NewAuthority(3, fake.NewSigner))
	require.Equal(t, 3, roster.Len())
}

func TestRoster_GetPublicKey(t *testing.T) {
	authority := fake.NewAuthority(3, fake.NewSigner)
	roster := FromAuthority(authority)

	iter := authority.AddressIterator()
	i := 0
	for iter.HasNext() {
		pubkey, index := roster.GetPublicKey(iter.GetNext())
		require.Equal(t, authority.GetSigner(i).GetPublicKey(), pubkey)
		require.Equal(t, i, index)
		i++
	}

	pubkey, index := roster.GetPublicKey(fake.NewAddress(999))
	require.Equal(t, -1, index)
	require.Nil(t, pubkey)
}

func TestRoster_AddressIterator(t *testing.T) {
	authority := fake.NewAuthority(3, fake.NewSigner)
	roster := FromAuthority(authority)

	iter := roster.AddressIterator()
	for i := 0; iter.HasNext(); i++ {
		require.Equal(t, authority.GetAddress(i), iter.GetNext())
	}
}

func TestRoster_PublicKeyIterator(t *testing.T) {
	authority := fake.NewAuthority(3, bls.Generate)
	roster := FromAuthority(authority)

	iter := roster.PublicKeyIterator()
	for i := 0; iter.HasNext(); i++ {
		require.Equal(t, authority.GetSigner(i).GetPublicKey(), iter.GetNext())
	}
}

func TestRoster_Serialize(t *testing.T) {
	roster := Roster{}

	data, err := roster.Serialize(fake.NewContext())
	require.NoError(t, err)
	require.Equal(t, "fake format", string(data))

	_, err = roster.Serialize(fake.NewBadContext())
	require.EqualError(t, err, "couldn't encode roster: fake error")
}

func TestFactory_Deserialize(t *testing.T) {
	factory := NewFactory(fake.AddressFactory{}, fake.PublicKeyFactory{})

	msg, err := factory.Deserialize(fake.NewContext(), nil)
	require.NoError(t, err)
	require.Equal(t, Roster{}, msg)

	_, err = factory.Deserialize(fake.NewBadContext(), nil)
	require.EqualError(t, err, "couldn't decode roster: fake error")

	_, err = factory.Deserialize(fake.NewContextWithFormat(serde.Format("BAD_TYPE")), nil)
	require.EqualError(t, err, "invalid message of type 'fake.Message'")
}
