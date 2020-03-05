// Code generated by protoc-gen-go. DO NOT EDIT.
// source: messages.proto

package blockchain

import (
	fmt "fmt"
	proto "github.com/golang/protobuf/proto"
	any "github.com/golang/protobuf/ptypes/any"
	mino "go.dedis.ch/fabric/mino"
	math "math"
)

// Reference imports to suppress errors if they are not otherwise used.
var _ = proto.Marshal
var _ = fmt.Errorf
var _ = math.Inf

// This is a compile-time assertion to ensure that this generated file
// is compatible with the proto package it is being compiled against.
// A compilation error at this line likely means your copy of the
// proto package needs to be updated.
const _ = proto.ProtoPackageIsVersion3 // please upgrade the proto package

type Conode struct {
	Address              *mino.Address `protobuf:"bytes,1,opt,name=address,proto3" json:"address,omitempty"`
	PublicKey            *any.Any      `protobuf:"bytes,2,opt,name=publicKey,proto3" json:"publicKey,omitempty"`
	XXX_NoUnkeyedLiteral struct{}      `json:"-"`
	XXX_unrecognized     []byte        `json:"-"`
	XXX_sizecache        int32         `json:"-"`
}

func (m *Conode) Reset()         { *m = Conode{} }
func (m *Conode) String() string { return proto.CompactTextString(m) }
func (*Conode) ProtoMessage()    {}
func (*Conode) Descriptor() ([]byte, []int) {
	return fileDescriptor_4dc296cbfe5ffcd5, []int{0}
}

func (m *Conode) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_Conode.Unmarshal(m, b)
}
func (m *Conode) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_Conode.Marshal(b, m, deterministic)
}
func (m *Conode) XXX_Merge(src proto.Message) {
	xxx_messageInfo_Conode.Merge(m, src)
}
func (m *Conode) XXX_Size() int {
	return xxx_messageInfo_Conode.Size(m)
}
func (m *Conode) XXX_DiscardUnknown() {
	xxx_messageInfo_Conode.DiscardUnknown(m)
}

var xxx_messageInfo_Conode proto.InternalMessageInfo

func (m *Conode) GetAddress() *mino.Address {
	if m != nil {
		return m.Address
	}
	return nil
}

func (m *Conode) GetPublicKey() *any.Any {
	if m != nil {
		return m.PublicKey
	}
	return nil
}

func init() {
	proto.RegisterType((*Conode)(nil), "blockchain.Conode")
}

func init() { proto.RegisterFile("messages.proto", fileDescriptor_4dc296cbfe5ffcd5) }

var fileDescriptor_4dc296cbfe5ffcd5 = []byte{
	// 156 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0xe2, 0xe2, 0xcb, 0x4d, 0x2d, 0x2e,
	0x4e, 0x4c, 0x4f, 0x2d, 0xd6, 0x2b, 0x28, 0xca, 0x2f, 0xc9, 0x17, 0xe2, 0x4a, 0xca, 0xc9, 0x4f,
	0xce, 0x4e, 0xce, 0x48, 0xcc, 0xcc, 0x93, 0x92, 0x4c, 0xcf, 0xcf, 0x4f, 0xcf, 0x49, 0xd5, 0x07,
	0xcb, 0x24, 0x95, 0xa6, 0xe9, 0x27, 0xe6, 0x55, 0x42, 0x94, 0x49, 0x09, 0xe7, 0x66, 0xe6, 0xe5,
	0xeb, 0xa3, 0xea, 0x55, 0x4a, 0xe5, 0x62, 0x73, 0xce, 0xcf, 0xcb, 0x4f, 0x49, 0x15, 0x52, 0xe7,
	0x62, 0x4f, 0x4c, 0x49, 0x29, 0x4a, 0x2d, 0x2e, 0x96, 0x60, 0x54, 0x60, 0xd4, 0xe0, 0x36, 0xe2,
	0xd5, 0x03, 0x69, 0xd0, 0x73, 0x84, 0x08, 0x06, 0xc1, 0x64, 0x85, 0x8c, 0xb8, 0x38, 0x0b, 0x4a,
	0x93, 0x72, 0x32, 0x93, 0xbd, 0x53, 0x2b, 0x25, 0x98, 0xc0, 0x4a, 0x45, 0xf4, 0x20, 0xd6, 0xea,
	0xc1, 0xac, 0xd5, 0x73, 0xcc, 0xab, 0x0c, 0x42, 0x28, 0x4b, 0x62, 0x03, 0x4b, 0x18, 0x03, 0x02,
	0x00, 0x00, 0xff, 0xff, 0xb0, 0x43, 0xf9, 0xb3, 0xbb, 0x00, 0x00, 0x00,
}
