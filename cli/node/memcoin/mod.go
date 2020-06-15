// Package main implements a ledger based on in-memory components.
package main

import (
	"os"

	"go.dedis.ch/dela/cli/node"
	byzcoin "go.dedis.ch/dela/ledger/byzcoin/controller"
	mino "go.dedis.ch/dela/mino/minogrpc/controller"
)

func main() {
	builder := node.NewBuilder(mino.NewMinimal(), byzcoin.NewMinimal())

	app := builder.Build()

	err := app.Run(os.Args)
	if err != nil {
		panic(err)
	}
}
