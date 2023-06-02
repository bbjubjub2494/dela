package pedersen

import (
	"encoding/csv"
	"flag"
	"fmt"
	"log"
	"math/rand"
	"os"
	"strconv"
	"time"
	"testing"

	"github.com/stretchr/testify/require"

	"go.dedis.ch/dela/dkg"
	"go.dedis.ch/dela/mino"

	"go.dedis.ch/dela/mino/minogrpc"
	"go.dedis.ch/dela/mino/router/tree"

	"go.dedis.ch/kyber/v3"
)

var nFlag = flag.String("n", "", "the number of committee members")

func Test_IBE_records(t *testing.T) {

	file, err := os.OpenFile("IBE_records.csv", os.O_WRONLY|os.O_CREATE|os.O_APPEND, 0644)
	defer file.Close()
	if err != nil {
		log.Fatalln("failed to open file", err)
	}
	w := csv.NewWriter(file)

	n, err := strconv.Atoi(*nFlag)
	if err != nil {
		panic("not n right argument")
	}

	threshold := n

	row := []string{strconv.Itoa(n)}

	minos := make([]mino.Mino, n)
	dkgs := make([]dkg.DKG, n)
	addrs := make([]mino.Address, n)

	fmt.Println("initiating the dkg nodes ...")
	for i := 0; i < n; i++ {
		addr := minogrpc.ParseAddress("127.0.0.1", 0)

		minogrpc, err := minogrpc.NewMinogrpc(addr, nil, tree.NewRouter(minogrpc.NewAddressFactory()))
		require.NoError(t, err)

		defer minogrpc.GracefulStop()

		minos[i] = minogrpc
		addrs[i] = minogrpc.GetAddress()
	}

	pubkeys := make([]kyber.Point, len(minos))

	for i, mino := range minos {
		for _, m := range minos {
			mino.(*minogrpc.Minogrpc).GetCertificateStore().Store(m.GetAddress(), m.(*minogrpc.Minogrpc).GetCertificateChain())
		}
		dkg, pubkey := NewPedersen(mino.(*minogrpc.Minogrpc))
		dkgs[i] = dkg
		pubkeys[i] = pubkey
	}

	fakeAuthority := NewAuthority(addrs, pubkeys)

	actors := make([]dkg.Actor, n)
	for i := 0; i < n; i++ {
		actor, err := dkgs[i].Listen()
		require.NoError(t, err)
		actors[i] = actor
	}

	w.Write([]string{"n","dkgTime","recvTime","combineTime"})
	fmt.Println("setting up the dkg ...")
	start := time.Now()
	_, err = actors[0].Setup(fakeAuthority, threshold)
	require.NoError(t, err)
	dkgTime := time.Since(start).Milliseconds()
	row = append(row, strconv.Itoa(int(dkgTime)))

	//generating random messages in batch and encrypt them

	const letterBytes = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
	msg := make([]byte, 29)
	for i := range msg {
		msg[i] = letterBytes[rand.Intn(len(letterBytes))]
	}
	_, recvTime, combineTime, err := actors[0].Sign(msg)
	require.NoError(t, err)
	row = append(row, strconv.Itoa(int(recvTime)))
	row = append(row, strconv.Itoa(int(combineTime)))

	if err := w.Write(row); err != nil {
		log.Fatalln("error writing record to file", err)
	}
	w.Flush()
	//}
}
