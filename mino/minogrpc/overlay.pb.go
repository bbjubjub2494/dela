// Code generated by protoc-gen-go. DO NOT EDIT.
// source: overlay.proto

package minogrpc

import (
	context "context"
	fmt "fmt"
	proto "github.com/golang/protobuf/proto"
	any "github.com/golang/protobuf/ptypes/any"
	grpc "google.golang.org/grpc"
	codes "google.golang.org/grpc/codes"
	status "google.golang.org/grpc/status"
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

// Envelope is wrapper around a message and one or several recipients.
type Envelope struct {
	From                 string   `protobuf:"bytes,1,opt,name=from,proto3" json:"from,omitempty"`
	To                   []string `protobuf:"bytes,2,rep,name=to,proto3" json:"to,omitempty"`
	Message              *any.Any `protobuf:"bytes,3,opt,name=message,proto3" json:"message,omitempty"`
	XXX_NoUnkeyedLiteral struct{} `json:"-"`
	XXX_unrecognized     []byte   `json:"-"`
	XXX_sizecache        int32    `json:"-"`
}

func (m *Envelope) Reset()         { *m = Envelope{} }
func (m *Envelope) String() string { return proto.CompactTextString(m) }
func (*Envelope) ProtoMessage()    {}
func (*Envelope) Descriptor() ([]byte, []int) {
	return fileDescriptor_61fc82527fbe24ad, []int{0}
}

func (m *Envelope) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_Envelope.Unmarshal(m, b)
}
func (m *Envelope) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_Envelope.Marshal(b, m, deterministic)
}
func (m *Envelope) XXX_Merge(src proto.Message) {
	xxx_messageInfo_Envelope.Merge(m, src)
}
func (m *Envelope) XXX_Size() int {
	return xxx_messageInfo_Envelope.Size(m)
}
func (m *Envelope) XXX_DiscardUnknown() {
	xxx_messageInfo_Envelope.DiscardUnknown(m)
}

var xxx_messageInfo_Envelope proto.InternalMessageInfo

func (m *Envelope) GetFrom() string {
	if m != nil {
		return m.From
	}
	return ""
}

func (m *Envelope) GetTo() []string {
	if m != nil {
		return m.To
	}
	return nil
}

func (m *Envelope) GetMessage() *any.Any {
	if m != nil {
		return m.Message
	}
	return nil
}

type CallMsg struct {
	Message              *any.Any `protobuf:"bytes,1,opt,name=message,proto3" json:"message,omitempty"`
	XXX_NoUnkeyedLiteral struct{} `json:"-"`
	XXX_unrecognized     []byte   `json:"-"`
	XXX_sizecache        int32    `json:"-"`
}

func (m *CallMsg) Reset()         { *m = CallMsg{} }
func (m *CallMsg) String() string { return proto.CompactTextString(m) }
func (*CallMsg) ProtoMessage()    {}
func (*CallMsg) Descriptor() ([]byte, []int) {
	return fileDescriptor_61fc82527fbe24ad, []int{1}
}

func (m *CallMsg) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_CallMsg.Unmarshal(m, b)
}
func (m *CallMsg) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_CallMsg.Marshal(b, m, deterministic)
}
func (m *CallMsg) XXX_Merge(src proto.Message) {
	xxx_messageInfo_CallMsg.Merge(m, src)
}
func (m *CallMsg) XXX_Size() int {
	return xxx_messageInfo_CallMsg.Size(m)
}
func (m *CallMsg) XXX_DiscardUnknown() {
	xxx_messageInfo_CallMsg.DiscardUnknown(m)
}

var xxx_messageInfo_CallMsg proto.InternalMessageInfo

func (m *CallMsg) GetMessage() *any.Any {
	if m != nil {
		return m.Message
	}
	return nil
}

type CallResp struct {
	Message              *any.Any `protobuf:"bytes,1,opt,name=message,proto3" json:"message,omitempty"`
	XXX_NoUnkeyedLiteral struct{} `json:"-"`
	XXX_unrecognized     []byte   `json:"-"`
	XXX_sizecache        int32    `json:"-"`
}

func (m *CallResp) Reset()         { *m = CallResp{} }
func (m *CallResp) String() string { return proto.CompactTextString(m) }
func (*CallResp) ProtoMessage()    {}
func (*CallResp) Descriptor() ([]byte, []int) {
	return fileDescriptor_61fc82527fbe24ad, []int{2}
}

func (m *CallResp) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_CallResp.Unmarshal(m, b)
}
func (m *CallResp) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_CallResp.Marshal(b, m, deterministic)
}
func (m *CallResp) XXX_Merge(src proto.Message) {
	xxx_messageInfo_CallResp.Merge(m, src)
}
func (m *CallResp) XXX_Size() int {
	return xxx_messageInfo_CallResp.Size(m)
}
func (m *CallResp) XXX_DiscardUnknown() {
	xxx_messageInfo_CallResp.DiscardUnknown(m)
}

var xxx_messageInfo_CallResp proto.InternalMessageInfo

func (m *CallResp) GetMessage() *any.Any {
	if m != nil {
		return m.Message
	}
	return nil
}

func init() {
	proto.RegisterType((*Envelope)(nil), "minogrpc.Envelope")
	proto.RegisterType((*CallMsg)(nil), "minogrpc.CallMsg")
	proto.RegisterType((*CallResp)(nil), "minogrpc.CallResp")
}

func init() { proto.RegisterFile("overlay.proto", fileDescriptor_61fc82527fbe24ad) }

var fileDescriptor_61fc82527fbe24ad = []byte{
	// 205 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x09, 0x6e, 0x88, 0x02, 0xff, 0xe2, 0xe2, 0xcd, 0x2f, 0x4b, 0x2d,
	0xca, 0x49, 0xac, 0xd4, 0x2b, 0x28, 0xca, 0x2f, 0xc9, 0x17, 0xe2, 0xc8, 0xcd, 0xcc, 0xcb, 0x4f,
	0x2f, 0x2a, 0x48, 0x96, 0x92, 0x4c, 0xcf, 0xcf, 0x4f, 0xcf, 0x49, 0xd5, 0x07, 0x8b, 0x27, 0x95,
	0xa6, 0xe9, 0x27, 0xe6, 0x41, 0x15, 0x29, 0xc5, 0x71, 0x71, 0xb8, 0xe6, 0x95, 0xa5, 0xe6, 0xe4,
	0x17, 0xa4, 0x0a, 0x09, 0x71, 0xb1, 0xa4, 0x15, 0xe5, 0xe7, 0x4a, 0x30, 0x2a, 0x30, 0x6a, 0x70,
	0x06, 0x81, 0xd9, 0x42, 0x7c, 0x5c, 0x4c, 0x25, 0xf9, 0x12, 0x4c, 0x0a, 0xcc, 0x40, 0x11, 0x20,
	0x4b, 0x48, 0x8f, 0x8b, 0x3d, 0x37, 0xb5, 0xb8, 0x38, 0x31, 0x3d, 0x55, 0x82, 0x19, 0xa8, 0x8c,
	0xdb, 0x48, 0x44, 0x0f, 0x62, 0xb8, 0x1e, 0xcc, 0x70, 0x3d, 0xc7, 0xbc, 0xca, 0x20, 0x98, 0x22,
	0x25, 0x4b, 0x2e, 0x76, 0xe7, 0xc4, 0x9c, 0x1c, 0xdf, 0xe2, 0x74, 0x64, 0xad, 0x8c, 0xc4, 0x68,
	0xb5, 0xe2, 0xe2, 0x00, 0x69, 0x0d, 0x4a, 0x2d, 0x2e, 0x20, 0x55, 0xaf, 0x91, 0x15, 0x17, 0xbb,
	0x3f, 0x24, 0x30, 0x84, 0xf4, 0xb9, 0x58, 0x40, 0xc6, 0x08, 0x09, 0xea, 0xc1, 0xc2, 0x43, 0x0f,
	0xea, 0x22, 0x29, 0x21, 0x54, 0x21, 0x90, 0x4d, 0x4a, 0x0c, 0x49, 0x6c, 0x60, 0x23, 0x8d, 0x01,
	0x01, 0x00, 0x00, 0xff, 0xff, 0xf2, 0x1c, 0x3f, 0xb5, 0x4f, 0x01, 0x00, 0x00,
}

// Reference imports to suppress errors if they are not otherwise used.
var _ context.Context
var _ grpc.ClientConn

// This is a compile-time assertion to ensure that this generated file
// is compatible with the grpc package it is being compiled against.
const _ = grpc.SupportPackageIsVersion4

// OverlayClient is the client API for Overlay service.
//
// For semantics around ctx use and closing/ending streaming RPCs, please refer to https://godoc.org/google.golang.org/grpc#ClientConn.NewStream.
type OverlayClient interface {
	Call(ctx context.Context, in *CallMsg, opts ...grpc.CallOption) (*CallResp, error)
}

type overlayClient struct {
	cc *grpc.ClientConn
}

func NewOverlayClient(cc *grpc.ClientConn) OverlayClient {
	return &overlayClient{cc}
}

func (c *overlayClient) Call(ctx context.Context, in *CallMsg, opts ...grpc.CallOption) (*CallResp, error) {
	out := new(CallResp)
	err := c.cc.Invoke(ctx, "/minogrpc.Overlay/Call", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

// OverlayServer is the server API for Overlay service.
type OverlayServer interface {
	Call(context.Context, *CallMsg) (*CallResp, error)
}

// UnimplementedOverlayServer can be embedded to have forward compatible implementations.
type UnimplementedOverlayServer struct {
}

func (*UnimplementedOverlayServer) Call(ctx context.Context, req *CallMsg) (*CallResp, error) {
	return nil, status.Errorf(codes.Unimplemented, "method Call not implemented")
}

func RegisterOverlayServer(s *grpc.Server, srv OverlayServer) {
	s.RegisterService(&_Overlay_serviceDesc, srv)
}

func _Overlay_Call_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(CallMsg)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(OverlayServer).Call(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/minogrpc.Overlay/Call",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(OverlayServer).Call(ctx, req.(*CallMsg))
	}
	return interceptor(ctx, in, info, handler)
}

var _Overlay_serviceDesc = grpc.ServiceDesc{
	ServiceName: "minogrpc.Overlay",
	HandlerType: (*OverlayServer)(nil),
	Methods: []grpc.MethodDesc{
		{
			MethodName: "Call",
			Handler:    _Overlay_Call_Handler,
		},
	},
	Streams:  []grpc.StreamDesc{},
	Metadata: "overlay.proto",
}
