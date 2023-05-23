#!/bin/bash

set -e

go install -buildvcs=false ./dkg/pedersen/dkgcli

TEMPDIR=$(mktemp -d /tmp/dkgcli.XXXXXXXXXXXXX)
rm_tempdir () {
 rm -rf "$TEMPDIR"
}
trap rm_tempdir EXIT

for i in $(seq 3); do
	tmux new-window -d "LLVL=info dkgcli --config $TEMPDIR/node$i start --listen tcp://127.0.0.1:$((2000+i)); read"
done

sleep 3

# Exchange certificates
for i in $(seq 2 3); do
	dkgcli --config $TEMPDIR/node$i minogrpc join --address //127.0.0.1:2001 $(dkgcli --config $TEMPDIR/node1 minogrpc token)
done

# Initialize DKG on each node. Do that in a 4th session.
for i in $(seq 3); do
	dkgcli --config $TEMPDIR/node$i dkg listen
done

# Do the setup in one of the node:
cmd=(dkgcli --config $TEMPDIR/node1 dkg setup) 
for i in $(seq 3); do
    cmd+=(--authority $(cat $TEMPDIR/node$i/dkgauthority))
done
"${cmd[@]}"

message=deadbeef # hexadecimal

# Sign with all 3 nodes for demo purposes
for i in $(seq 3); do
dkgcli --config $TEMPDIR/node$i dkg sign -message $message
done
