// Code generated by protoc-gen-go. DO NOT EDIT.
// source: messages.proto

package byzcoin

import (
	fmt "fmt"
	proto "github.com/golang/protobuf/proto"
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

// TransactionProto is the message that represents a transaction.
type TransactionProto struct {
	Value                string   `protobuf:"bytes,1,opt,name=value,proto3" json:"value,omitempty"`
	XXX_NoUnkeyedLiteral struct{} `json:"-"`
	XXX_unrecognized     []byte   `json:"-"`
	XXX_sizecache        int32    `json:"-"`
}

func (m *TransactionProto) Reset()         { *m = TransactionProto{} }
func (m *TransactionProto) String() string { return proto.CompactTextString(m) }
func (*TransactionProto) ProtoMessage()    {}
func (*TransactionProto) Descriptor() ([]byte, []int) {
	return fileDescriptor_4dc296cbfe5ffcd5, []int{0}
}

func (m *TransactionProto) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_TransactionProto.Unmarshal(m, b)
}
func (m *TransactionProto) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_TransactionProto.Marshal(b, m, deterministic)
}
func (m *TransactionProto) XXX_Merge(src proto.Message) {
	xxx_messageInfo_TransactionProto.Merge(m, src)
}
func (m *TransactionProto) XXX_Size() int {
	return xxx_messageInfo_TransactionProto.Size(m)
}
func (m *TransactionProto) XXX_DiscardUnknown() {
	xxx_messageInfo_TransactionProto.DiscardUnknown(m)
}

var xxx_messageInfo_TransactionProto proto.InternalMessageInfo

func (m *TransactionProto) GetValue() string {
	if m != nil {
		return m.Value
	}
	return ""
}

// BlockPayload is the message that will be stored in the blocks. It is composed
// of the transactions and the footprint of the new inventory.
type BlockPayload struct {
	Txs []*TransactionProto `protobuf:"bytes,1,rep,name=txs,proto3" json:"txs,omitempty"`
	// Footprint is an integrity check of the final state of the inventory after
	// applying the transactions.
	Footprint            []byte   `protobuf:"bytes,2,opt,name=footprint,proto3" json:"footprint,omitempty"`
	XXX_NoUnkeyedLiteral struct{} `json:"-"`
	XXX_unrecognized     []byte   `json:"-"`
	XXX_sizecache        int32    `json:"-"`
}

func (m *BlockPayload) Reset()         { *m = BlockPayload{} }
func (m *BlockPayload) String() string { return proto.CompactTextString(m) }
func (*BlockPayload) ProtoMessage()    {}
func (*BlockPayload) Descriptor() ([]byte, []int) {
	return fileDescriptor_4dc296cbfe5ffcd5, []int{1}
}

func (m *BlockPayload) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_BlockPayload.Unmarshal(m, b)
}
func (m *BlockPayload) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_BlockPayload.Marshal(b, m, deterministic)
}
func (m *BlockPayload) XXX_Merge(src proto.Message) {
	xxx_messageInfo_BlockPayload.Merge(m, src)
}
func (m *BlockPayload) XXX_Size() int {
	return xxx_messageInfo_BlockPayload.Size(m)
}
func (m *BlockPayload) XXX_DiscardUnknown() {
	xxx_messageInfo_BlockPayload.DiscardUnknown(m)
}

var xxx_messageInfo_BlockPayload proto.InternalMessageInfo

func (m *BlockPayload) GetTxs() []*TransactionProto {
	if m != nil {
		return m.Txs
	}
	return nil
}

func (m *BlockPayload) GetFootprint() []byte {
	if m != nil {
		return m.Footprint
	}
	return nil
}

func init() {
	proto.RegisterType((*TransactionProto)(nil), "byzcoin.TransactionProto")
	proto.RegisterType((*BlockPayload)(nil), "byzcoin.BlockPayload")
}

func init() {
	proto.RegisterFile("messages.proto", fileDescriptor_4dc296cbfe5ffcd5)
}

var fileDescriptor_4dc296cbfe5ffcd5 = []byte{
	// 151 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0xe2, 0xe2, 0xcb, 0x4d, 0x2d, 0x2e,
	0x4e, 0x4c, 0x4f, 0x2d, 0xd6, 0x2b, 0x28, 0xca, 0x2f, 0xc9, 0x17, 0x62, 0x4f, 0xaa, 0xac, 0x4a,
	0xce, 0xcf, 0xcc, 0x53, 0xd2, 0xe0, 0x12, 0x08, 0x29, 0x4a, 0xcc, 0x2b, 0x4e, 0x4c, 0x2e, 0xc9,
	0xcc, 0xcf, 0x0b, 0x00, 0x4b, 0x8a, 0x70, 0xb1, 0x96, 0x25, 0xe6, 0x94, 0xa6, 0x4a, 0x30, 0x2a,
	0x30, 0x6a, 0x70, 0x06, 0x41, 0x38, 0x4a, 0x91, 0x5c, 0x3c, 0x4e, 0x39, 0xf9, 0xc9, 0xd9, 0x01,
	0x89, 0x95, 0x39, 0xf9, 0x89, 0x29, 0x42, 0xda, 0x5c, 0xcc, 0x25, 0x15, 0xc5, 0x12, 0x8c, 0x0a,
	0xcc, 0x1a, 0xdc, 0x46, 0x92, 0x7a, 0x50, 0x03, 0xf5, 0xd0, 0x4d, 0x0b, 0x02, 0xa9, 0x12, 0x92,
	0xe1, 0xe2, 0x4c, 0xcb, 0xcf, 0x2f, 0x29, 0x28, 0xca, 0xcc, 0x2b, 0x91, 0x60, 0x52, 0x60, 0xd4,
	0xe0, 0x09, 0x42, 0x08, 0x24, 0xb1, 0x81, 0x1d, 0x65, 0x0c, 0x08, 0x00, 0x00, 0xff, 0xff, 0x33,
	0xa6, 0x6b, 0x0b, 0xa6, 0x00, 0x00, 0x00,
}
