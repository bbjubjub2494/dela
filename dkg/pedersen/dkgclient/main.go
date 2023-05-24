package main

import (
	"fmt"
	"encoding/hex"
	"go.dedis.ch/dela/crypto/bls"
)

func main() {
	pkBytes, err := hex.DecodeString("3173227d62eaed4e184f865ad529392b3b2af161d7c607c7a00ece16772203260d813383367104394da2c171673b4f9ad95ffe803685979607fba0733911061b8d1307f9b5dcdcda98f58550c3a86970b579130c8f74f00457c5de80d09deec887a00767e6b54d91b3589c58b353b1dd483850aaa50c6a54c5a33576628f2d37")
	if err != nil {
		panic(err)
	}
	pk, err := bls.NewPublicKey(pkBytes)
	if err != nil {
		panic(err)
	}
	sigBytes, err := hex.DecodeString("0cf734952c3167fce38e24c27d7ea325267e278ea70587661eb0aa481de9f74780e51d33ea2d12902d6adf7e000ce49907a69aef789e70442989eb1d0feb8924")
	if err != nil {
		panic(err)
	}
	fmt.Println(pk)
	fmt.Println(sigBytes)
}
