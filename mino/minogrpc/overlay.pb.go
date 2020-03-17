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

type OverlayMsg struct {
	Message              *any.Any `protobuf:"bytes,1,opt,name=message,proto3" json:"message,omitempty"`
	XXX_NoUnkeyedLiteral struct{} `json:"-"`
	XXX_unrecognized     []byte   `json:"-"`
	XXX_sizecache        int32    `json:"-"`
}

func (m *OverlayMsg) Reset()         { *m = OverlayMsg{} }
func (m *OverlayMsg) String() string { return proto.CompactTextString(m) }
func (*OverlayMsg) ProtoMessage()    {}
func (*OverlayMsg) Descriptor() ([]byte, []int) {
	return fileDescriptor_61fc82527fbe24ad, []int{1}
}

func (m *OverlayMsg) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_OverlayMsg.Unmarshal(m, b)
}
func (m *OverlayMsg) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_OverlayMsg.Marshal(b, m, deterministic)
}
func (m *OverlayMsg) XXX_Merge(src proto.Message) {
	xxx_messageInfo_OverlayMsg.Merge(m, src)
}
func (m *OverlayMsg) XXX_Size() int {
	return xxx_messageInfo_OverlayMsg.Size(m)
}
func (m *OverlayMsg) XXX_DiscardUnknown() {
	xxx_messageInfo_OverlayMsg.DiscardUnknown(m)
}

var xxx_messageInfo_OverlayMsg proto.InternalMessageInfo

func (m *OverlayMsg) GetMessage() *any.Any {
	if m != nil {
		return m.Message
	}
	return nil
}

type DummyMsg struct {
	Value                string   `protobuf:"bytes,1,opt,name=value,proto3" json:"value,omitempty"`
	XXX_NoUnkeyedLiteral struct{} `json:"-"`
	XXX_unrecognized     []byte   `json:"-"`
	XXX_sizecache        int32    `json:"-"`
}

func (m *DummyMsg) Reset()         { *m = DummyMsg{} }
func (m *DummyMsg) String() string { return proto.CompactTextString(m) }
func (*DummyMsg) ProtoMessage()    {}
func (*DummyMsg) Descriptor() ([]byte, []int) {
	return fileDescriptor_61fc82527fbe24ad, []int{2}
}

func (m *DummyMsg) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_DummyMsg.Unmarshal(m, b)
}
func (m *DummyMsg) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_DummyMsg.Marshal(b, m, deterministic)
}
func (m *DummyMsg) XXX_Merge(src proto.Message) {
	xxx_messageInfo_DummyMsg.Merge(m, src)
}
func (m *DummyMsg) XXX_Size() int {
	return xxx_messageInfo_DummyMsg.Size(m)
}
func (m *DummyMsg) XXX_DiscardUnknown() {
	xxx_messageInfo_DummyMsg.DiscardUnknown(m)
}

var xxx_messageInfo_DummyMsg proto.InternalMessageInfo

func (m *DummyMsg) GetValue() string {
	if m != nil {
		return m.Value
	}
	return ""
}

func init() {
	proto.RegisterType((*Envelope)(nil), "minogrpc.Envelope")
	proto.RegisterType((*OverlayMsg)(nil), "minogrpc.OverlayMsg")
	proto.RegisterType((*DummyMsg)(nil), "minogrpc.DummyMsg")
}

func init() { proto.RegisterFile("overlay.proto", fileDescriptor_61fc82527fbe24ad) }

var fileDescriptor_61fc82527fbe24ad = []byte{
	// 230 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x94, 0x8f, 0x31, 0x4b, 0xc4, 0x40,
	0x10, 0x85, 0xdd, 0xdc, 0x79, 0x97, 0x1b, 0xd1, 0x62, 0x48, 0x11, 0xaf, 0x0a, 0xa9, 0x52, 0xed,
	0xc9, 0x69, 0x25, 0x36, 0xa2, 0x96, 0x22, 0xc4, 0x5e, 0xd8, 0x93, 0xb9, 0x45, 0xd8, 0xdd, 0x09,
	0x9b, 0x4d, 0x20, 0xf8, 0xe7, 0x85, 0x4d, 0x82, 0x16, 0x16, 0xda, 0xcd, 0x3c, 0xde, 0xf7, 0xe6,
	0x0d, 0x9c, 0x73, 0x4f, 0xde, 0xa8, 0x41, 0x36, 0x9e, 0x03, 0x63, 0x6a, 0x3f, 0x1c, 0x6b, 0xdf,
	0xbc, 0x6f, 0x2f, 0x35, 0xb3, 0x36, 0xb4, 0x8b, 0xfa, 0xa1, 0x3b, 0xee, 0x94, 0x9b, 0x4c, 0xe5,
	0x1b, 0xa4, 0x4f, 0xae, 0x27, 0xc3, 0x0d, 0x21, 0xc2, 0xf2, 0xe8, 0xd9, 0xe6, 0xa2, 0x10, 0xd5,
	0xa6, 0x8e, 0x33, 0x5e, 0x40, 0x12, 0x38, 0x4f, 0x8a, 0x45, 0xb5, 0xa9, 0x93, 0xc0, 0x28, 0x61,
	0x6d, 0xa9, 0x6d, 0x95, 0xa6, 0x7c, 0x51, 0x88, 0xea, 0x6c, 0x9f, 0xc9, 0x31, 0x5c, 0xce, 0xe1,
	0xf2, 0xde, 0x0d, 0xf5, 0x6c, 0x2a, 0xef, 0x00, 0x5e, 0xc6, 0x56, 0xcf, 0xad, 0xfe, 0x49, 0x8b,
	0xbf, 0xd0, 0x05, 0xa4, 0x8f, 0x9d, 0xb5, 0x91, 0xcd, 0xe0, 0xb4, 0x57, 0xa6, 0xa3, 0xa9, 0xde,
	0xb8, 0xec, 0x3f, 0x61, 0x3d, 0xe5, 0xe3, 0x0d, 0x2c, 0x1f, 0x94, 0x31, 0x98, 0xc9, 0xf9, 0x71,
	0xf9, 0x7d, 0x7a, 0xfb, 0xab, 0x5a, 0x9e, 0xe0, 0x2d, 0xac, 0x5e, 0x83, 0x27, 0x65, 0xff, 0xc7,
	0x55, 0xe2, 0x4a, 0x1c, 0x56, 0xb1, 0xf5, 0xf5, 0x57, 0x00, 0x00, 0x00, 0xff, 0xff, 0x59, 0xf6,
	0x2c, 0x53, 0x79, 0x01, 0x00, 0x00,
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
	Call(ctx context.Context, in *OverlayMsg, opts ...grpc.CallOption) (*OverlayMsg, error)
	Stream(ctx context.Context, opts ...grpc.CallOption) (Overlay_StreamClient, error)
}

type overlayClient struct {
	cc *grpc.ClientConn
}

func NewOverlayClient(cc *grpc.ClientConn) OverlayClient {
	return &overlayClient{cc}
}

func (c *overlayClient) Call(ctx context.Context, in *OverlayMsg, opts ...grpc.CallOption) (*OverlayMsg, error) {
	out := new(OverlayMsg)
	err := c.cc.Invoke(ctx, "/minogrpc.Overlay/Call", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *overlayClient) Stream(ctx context.Context, opts ...grpc.CallOption) (Overlay_StreamClient, error) {
	stream, err := c.cc.NewStream(ctx, &_Overlay_serviceDesc.Streams[0], "/minogrpc.Overlay/Stream", opts...)
	if err != nil {
		return nil, err
	}
	x := &overlayStreamClient{stream}
	return x, nil
}

type Overlay_StreamClient interface {
	Send(*OverlayMsg) error
	Recv() (*OverlayMsg, error)
	grpc.ClientStream
}

type overlayStreamClient struct {
	grpc.ClientStream
}

func (x *overlayStreamClient) Send(m *OverlayMsg) error {
	return x.ClientStream.SendMsg(m)
}

func (x *overlayStreamClient) Recv() (*OverlayMsg, error) {
	m := new(OverlayMsg)
	if err := x.ClientStream.RecvMsg(m); err != nil {
		return nil, err
	}
	return m, nil
}

// OverlayServer is the server API for Overlay service.
type OverlayServer interface {
	Call(context.Context, *OverlayMsg) (*OverlayMsg, error)
	Stream(Overlay_StreamServer) error
}

// UnimplementedOverlayServer can be embedded to have forward compatible implementations.
type UnimplementedOverlayServer struct {
}

func (*UnimplementedOverlayServer) Call(ctx context.Context, req *OverlayMsg) (*OverlayMsg, error) {
	return nil, status.Errorf(codes.Unimplemented, "method Call not implemented")
}
func (*UnimplementedOverlayServer) Stream(srv Overlay_StreamServer) error {
	return status.Errorf(codes.Unimplemented, "method Stream not implemented")
}

func RegisterOverlayServer(s *grpc.Server, srv OverlayServer) {
	s.RegisterService(&_Overlay_serviceDesc, srv)
}

func _Overlay_Call_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(OverlayMsg)
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
		return srv.(OverlayServer).Call(ctx, req.(*OverlayMsg))
	}
	return interceptor(ctx, in, info, handler)
}

func _Overlay_Stream_Handler(srv interface{}, stream grpc.ServerStream) error {
	return srv.(OverlayServer).Stream(&overlayStreamServer{stream})
}

type Overlay_StreamServer interface {
	Send(*OverlayMsg) error
	Recv() (*OverlayMsg, error)
	grpc.ServerStream
}

type overlayStreamServer struct {
	grpc.ServerStream
}

func (x *overlayStreamServer) Send(m *OverlayMsg) error {
	return x.ServerStream.SendMsg(m)
}

func (x *overlayStreamServer) Recv() (*OverlayMsg, error) {
	m := new(OverlayMsg)
	if err := x.ServerStream.RecvMsg(m); err != nil {
		return nil, err
	}
	return m, nil
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
	Streams: []grpc.StreamDesc{
		{
			StreamName:    "Stream",
			Handler:       _Overlay_Stream_Handler,
			ServerStreams: true,
			ClientStreams: true,
		},
	},
	Metadata: "overlay.proto",
}
