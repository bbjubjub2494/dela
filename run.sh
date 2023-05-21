#!/bin/sh

set -e

go install ./dkg/pedersen/dkgcli

TEMPDIR=$(mktemp -d /tmp/dkgcli.XXXXXXXXXXXXX)
function rm_tempdir {
 rm -rf "$TEMPDIR"
}
trap rm_tempdir EXIT

tmux new-window -d "LLVL=info dkgcli --config $TEMPDIR/node1 start --listen tcp://127.0.0.1:2001; read"
tmux new-window -d "LLVL=info dkgcli --config $TEMPDIR/node2 start --listen tcp://127.0.0.1:2002; read"
tmux new-window -d "LLVL=info dkgcli --config $TEMPDIR/node3 start --listen tcp://127.0.0.1:2003; read"

sleep 3

# Exchange certificates
dkgcli --config $TEMPDIR/node2 minogrpc join --address //127.0.0.1:2001 $(dkgcli --config $TEMPDIR/node1 minogrpc token)
dkgcli --config $TEMPDIR/node3 minogrpc join --address //127.0.0.1:2001 $(dkgcli --config $TEMPDIR/node1 minogrpc token)

# Initialize DKG on each node. Do that in a 4th session.
dkgcli --config $TEMPDIR/node1 dkg listen
dkgcli --config $TEMPDIR/node2 dkg listen
dkgcli --config $TEMPDIR/node3 dkg listen

# Do the setup in one of the node:
dkgcli --config $TEMPDIR/node1 dkg setup \
    --authority $(cat $TEMPDIR/node1/dkgauthority) \
    --authority $(cat $TEMPDIR/node2/dkgauthority) \
    --authority $(cat $TEMPDIR/node3/dkgauthority)


message=deadbeef # hexadecimal

# Do the setup in one of the node:
dkgcli --config $TEMPDIR/node1 dkg sign $message
