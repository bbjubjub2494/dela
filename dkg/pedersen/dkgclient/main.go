package main

import (
	"fmt"
	"os"
	"os/exec"
	"encoding/hex"
	"strings"

	"go.dedis.ch/dela/crypto/bls"
)

func main() {
	cmd := exec.Command("dkgcli", "--config", os.ExpandEnv("$TEMPDIR/node1"), "dkg", "get-public-key")
	pkHex, err := cmd.Output()
	if err != nil {
		panic(err)
	}
	fmt.Println(string(pkHex))
	pkBytes, err := hex.DecodeString(strings.TrimSpace(string(pkHex)))
	if err != nil {
		panic(err)
	}
	pk, err := bls.NewPublicKey(pkBytes)
	if err != nil {
		panic(err)
	}
	message, err := hex.DecodeString("deadbeef")
	if err != nil {
		panic(err)
	}
	cmd = exec.Command("dkgcli", "--config", os.ExpandEnv("$TEMPDIR/node1"), "dkg", "sign", "-message", hex.EncodeToString(message))
	sigHex, err := cmd.Output()
	sigBytes, err := hex.DecodeString(strings.TrimSpace(string(sigHex)))
	if err != nil {
		panic(err)
	}
	sig := bls.NewSignature(sigBytes)

	err = pk.Verify(message, sig)
	if err != nil {
		panic(err)
	}
}
