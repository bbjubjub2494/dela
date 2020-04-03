// Code generated by protoc-gen-go. DO NOT EDIT.
// source: messages.proto

package darc

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

type Expression struct {
	Matches              []string `protobuf:"bytes,1,rep,name=matches,proto3" json:"matches,omitempty"`
	XXX_NoUnkeyedLiteral struct{} `json:"-"`
	XXX_unrecognized     []byte   `json:"-"`
	XXX_sizecache        int32    `json:"-"`
}

func (m *Expression) Reset()         { *m = Expression{} }
func (m *Expression) String() string { return proto.CompactTextString(m) }
func (*Expression) ProtoMessage()    {}
func (*Expression) Descriptor() ([]byte, []int) {
	return fileDescriptor_4dc296cbfe5ffcd5, []int{0}
}

func (m *Expression) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_Expression.Unmarshal(m, b)
}
func (m *Expression) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_Expression.Marshal(b, m, deterministic)
}
func (m *Expression) XXX_Merge(src proto.Message) {
	xxx_messageInfo_Expression.Merge(m, src)
}
func (m *Expression) XXX_Size() int {
	return xxx_messageInfo_Expression.Size(m)
}
func (m *Expression) XXX_DiscardUnknown() {
	xxx_messageInfo_Expression.DiscardUnknown(m)
}

var xxx_messageInfo_Expression proto.InternalMessageInfo

func (m *Expression) GetMatches() []string {
	if m != nil {
		return m.Matches
	}
	return nil
}

type AccessControlProto struct {
	Rules                map[string]*Expression `protobuf:"bytes,1,rep,name=rules,proto3" json:"rules,omitempty" protobuf_key:"bytes,1,opt,name=key,proto3" protobuf_val:"bytes,2,opt,name=value,proto3"`
	XXX_NoUnkeyedLiteral struct{}               `json:"-"`
	XXX_unrecognized     []byte                 `json:"-"`
	XXX_sizecache        int32                  `json:"-"`
}

func (m *AccessControlProto) Reset()         { *m = AccessControlProto{} }
func (m *AccessControlProto) String() string { return proto.CompactTextString(m) }
func (*AccessControlProto) ProtoMessage()    {}
func (*AccessControlProto) Descriptor() ([]byte, []int) {
	return fileDescriptor_4dc296cbfe5ffcd5, []int{1}
}

func (m *AccessControlProto) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_AccessControlProto.Unmarshal(m, b)
}
func (m *AccessControlProto) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_AccessControlProto.Marshal(b, m, deterministic)
}
func (m *AccessControlProto) XXX_Merge(src proto.Message) {
	xxx_messageInfo_AccessControlProto.Merge(m, src)
}
func (m *AccessControlProto) XXX_Size() int {
	return xxx_messageInfo_AccessControlProto.Size(m)
}
func (m *AccessControlProto) XXX_DiscardUnknown() {
	xxx_messageInfo_AccessControlProto.DiscardUnknown(m)
}

var xxx_messageInfo_AccessControlProto proto.InternalMessageInfo

func (m *AccessControlProto) GetRules() map[string]*Expression {
	if m != nil {
		return m.Rules
	}
	return nil
}

func init() {
	proto.RegisterType((*Expression)(nil), "darc.Expression")
	proto.RegisterType((*AccessControlProto)(nil), "darc.AccessControlProto")
	proto.RegisterMapType((map[string]*Expression)(nil), "darc.AccessControlProto.RulesEntry")
}

func init() {
	proto.RegisterFile("messages.proto", fileDescriptor_4dc296cbfe5ffcd5)
}

var fileDescriptor_4dc296cbfe5ffcd5 = []byte{
	// 185 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0xe2, 0xe2, 0xcb, 0x4d, 0x2d, 0x2e,
	0x4e, 0x4c, 0x4f, 0x2d, 0xd6, 0x2b, 0x28, 0xca, 0x2f, 0xc9, 0x17, 0x62, 0x49, 0x49, 0x2c, 0x4a,
	0x56, 0x52, 0xe3, 0xe2, 0x72, 0xad, 0x28, 0x28, 0x4a, 0x2d, 0x2e, 0xce, 0xcc, 0xcf, 0x13, 0x92,
	0xe0, 0x62, 0xcf, 0x4d, 0x2c, 0x49, 0xce, 0x48, 0x2d, 0x96, 0x60, 0x54, 0x60, 0xd6, 0xe0, 0x0c,
	0x82, 0x71, 0x95, 0x66, 0x33, 0x72, 0x09, 0x39, 0x26, 0x27, 0xa7, 0x16, 0x17, 0x3b, 0xe7, 0xe7,
	0x95, 0x14, 0xe5, 0xe7, 0x04, 0x80, 0x0d, 0xb1, 0xe4, 0x62, 0x2d, 0x2a, 0xcd, 0x81, 0x2a, 0xe7,
	0x36, 0x52, 0xd6, 0x03, 0x19, 0xaa, 0x87, 0xa9, 0x50, 0x2f, 0x08, 0xa4, 0xca, 0x35, 0xaf, 0xa4,
	0xa8, 0x32, 0x08, 0xa2, 0x43, 0xca, 0x8b, 0x8b, 0x0b, 0x21, 0x28, 0x24, 0xc0, 0xc5, 0x9c, 0x9d,
	0x5a, 0x29, 0xc1, 0xa8, 0xc0, 0xa8, 0xc1, 0x19, 0x04, 0x62, 0x0a, 0xa9, 0x71, 0xb1, 0x96, 0x25,
	0xe6, 0x94, 0xa6, 0x4a, 0x30, 0x29, 0x30, 0x6a, 0x70, 0x1b, 0x09, 0x40, 0x8c, 0x46, 0x38, 0x36,
	0x08, 0x22, 0x6d, 0xc5, 0x64, 0xc1, 0x98, 0xc4, 0x06, 0xf6, 0x92, 0x31, 0x20, 0x00, 0x00, 0xff,
	0xff, 0x5b, 0x87, 0x53, 0x5c, 0xe4, 0x00, 0x00, 0x00,
}
