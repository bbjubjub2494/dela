// Package router defines the primitives to route a packet among a set of
// participants.
package router

import (
	"go.dedis.ch/dela/mino"
	"go.dedis.ch/dela/serde"
)

// PacketFactory describes the primitives to deserialize a packet
type PacketFactory interface {
	serde.Factory
	PacketOf(serde.Context, []byte) (Packet, error)
}

// Membership describes the primitives to know what nodes the node knows
type Membership interface {
	GetLocal() mino.Address
	GetAddresses() []mino.Address
}

// Packet is the type of message processed by the router. It contains
// information that will allow the message to be routed.
type Packet interface {
	serde.Message

	// GetSource returns the source address of the message.
	GetSource() mino.Address

	// GetDestination returns the destination address of the message.
	GetDestination() []mino.Address

	// GetMessage returns the message to be transmitted to the application when
	// the source address is the current node. Message is only deserialized when
	// needed.
	GetMessage() []byte

	// Slice removes the address from the destination if found and return a new
	// packet with the addr as the destination. If not found return nil.
	Slice(addr mino.Address) Packet
}

// Router is the interface of the routing service. It provides the primitives to
// route a packet among a set of participants. The orchestrator address (if any)
// is not handled by the router. For that matter, the Packet.Slice function can
// be used to handle special cases with that address.
type Router interface {
	GetPacketFactory() PacketFactory

	// MakePacket should be first called by the caller to set the specific
	// required attribute on the packet if needed, for example a seed.
	MakePacket(me mino.Address, to []mino.Address, msg []byte) Packet

	// Forward takes the destination address, unmarshal the packet, and, based
	// on its content, return a map of packets, where each element of the map
	// represents the destination as the key, and the packet to send as the
	// value. The simplest forward would be, if the destination is A,B,C, to
	// create a map with 3 entries:
	//
	//  {A: packet{to: [A]}, B: packet{to: [B]}, C: packet{to: [C]}}.
	//
	// For a tree routing, the first message will send a packet with all the
	// recipients to the root address (A in the following), like:
	//
	//	{A: packet{to: [A, B, C]}}
	//
	Forward(memship Membership, packet Packet) (map[mino.Address]Packet, error)

	// OnFailure is used to announce that a packet failed to be routed. It
	// allows the router to find a different route. Forward can be called
	// afterwards to find an alternative route.
	OnFailure(to mino.Address) error
}
