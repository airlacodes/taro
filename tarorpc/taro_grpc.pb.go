// Code generated by protoc-gen-go-grpc. DO NOT EDIT.

package tarorpc

import (
	context "context"
	grpc "google.golang.org/grpc"
	codes "google.golang.org/grpc/codes"
	status "google.golang.org/grpc/status"
)

// This is a compile-time assertion to ensure that this generated file
// is compatible with the grpc package it is being compiled against.
// Requires gRPC-Go v1.32.0 or later.
const _ = grpc.SupportPackageIsVersion7

// TaroClient is the client API for Taro service.
//
// For semantics around ctx use and closing/ending streaming RPCs, please refer to https://pkg.go.dev/google.golang.org/grpc/?tab=doc#ClientConn.NewStream.
type TaroClient interface {
	// tarocli: `assets list`
	//MintAsset will attempts to mint the set of assets (async by default to
	//ensure proper batching) specified in the request.
	MintAsset(ctx context.Context, in *MintAssetRequest, opts ...grpc.CallOption) (*MintAssetResponse, error)
	// tarocli: `assets mint`
	//ListAssets lists the set of assets owned by the target daemon.
	ListAssets(ctx context.Context, in *ListAssetRequest, opts ...grpc.CallOption) (*ListAssetResponse, error)
	// tarocli: `stop`
	//StopDaemon will send a shutdown request to the interrupt handler, triggering
	//a graceful shutdown of the daemon.
	StopDaemon(ctx context.Context, in *StopRequest, opts ...grpc.CallOption) (*StopResponse, error)
	// tarocli: `debuglevel`
	//DebugLevel allows a caller to programmatically set the logging verbosity of
	//tarod. The logging can be targeted according to a coarse daemon-wide logging
	//level, or in a granular fashion to specify the logging for a target
	//sub-system.
	DebugLevel(ctx context.Context, in *DebugLevelRequest, opts ...grpc.CallOption) (*DebugLevelResponse, error)
}

type taroClient struct {
	cc grpc.ClientConnInterface
}

func NewTaroClient(cc grpc.ClientConnInterface) TaroClient {
	return &taroClient{cc}
}

func (c *taroClient) MintAsset(ctx context.Context, in *MintAssetRequest, opts ...grpc.CallOption) (*MintAssetResponse, error) {
	out := new(MintAssetResponse)
	err := c.cc.Invoke(ctx, "/tarorpc.Taro/MintAsset", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *taroClient) ListAssets(ctx context.Context, in *ListAssetRequest, opts ...grpc.CallOption) (*ListAssetResponse, error) {
	out := new(ListAssetResponse)
	err := c.cc.Invoke(ctx, "/tarorpc.Taro/ListAssets", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *taroClient) StopDaemon(ctx context.Context, in *StopRequest, opts ...grpc.CallOption) (*StopResponse, error) {
	out := new(StopResponse)
	err := c.cc.Invoke(ctx, "/tarorpc.Taro/StopDaemon", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *taroClient) DebugLevel(ctx context.Context, in *DebugLevelRequest, opts ...grpc.CallOption) (*DebugLevelResponse, error) {
	out := new(DebugLevelResponse)
	err := c.cc.Invoke(ctx, "/tarorpc.Taro/DebugLevel", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

// TaroServer is the server API for Taro service.
// All implementations must embed UnimplementedTaroServer
// for forward compatibility
type TaroServer interface {
	// tarocli: `assets list`
	//MintAsset will attempts to mint the set of assets (async by default to
	//ensure proper batching) specified in the request.
	MintAsset(context.Context, *MintAssetRequest) (*MintAssetResponse, error)
	// tarocli: `assets mint`
	//ListAssets lists the set of assets owned by the target daemon.
	ListAssets(context.Context, *ListAssetRequest) (*ListAssetResponse, error)
	// tarocli: `stop`
	//StopDaemon will send a shutdown request to the interrupt handler, triggering
	//a graceful shutdown of the daemon.
	StopDaemon(context.Context, *StopRequest) (*StopResponse, error)
	// tarocli: `debuglevel`
	//DebugLevel allows a caller to programmatically set the logging verbosity of
	//tarod. The logging can be targeted according to a coarse daemon-wide logging
	//level, or in a granular fashion to specify the logging for a target
	//sub-system.
	DebugLevel(context.Context, *DebugLevelRequest) (*DebugLevelResponse, error)
	mustEmbedUnimplementedTaroServer()
}

// UnimplementedTaroServer must be embedded to have forward compatible implementations.
type UnimplementedTaroServer struct {
}

func (UnimplementedTaroServer) MintAsset(context.Context, *MintAssetRequest) (*MintAssetResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method MintAsset not implemented")
}
func (UnimplementedTaroServer) ListAssets(context.Context, *ListAssetRequest) (*ListAssetResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method ListAssets not implemented")
}
func (UnimplementedTaroServer) StopDaemon(context.Context, *StopRequest) (*StopResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method StopDaemon not implemented")
}
func (UnimplementedTaroServer) DebugLevel(context.Context, *DebugLevelRequest) (*DebugLevelResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method DebugLevel not implemented")
}
func (UnimplementedTaroServer) mustEmbedUnimplementedTaroServer() {}

// UnsafeTaroServer may be embedded to opt out of forward compatibility for this service.
// Use of this interface is not recommended, as added methods to TaroServer will
// result in compilation errors.
type UnsafeTaroServer interface {
	mustEmbedUnimplementedTaroServer()
}

func RegisterTaroServer(s grpc.ServiceRegistrar, srv TaroServer) {
	s.RegisterService(&Taro_ServiceDesc, srv)
}

func _Taro_MintAsset_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(MintAssetRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(TaroServer).MintAsset(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/tarorpc.Taro/MintAsset",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(TaroServer).MintAsset(ctx, req.(*MintAssetRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _Taro_ListAssets_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(ListAssetRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(TaroServer).ListAssets(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/tarorpc.Taro/ListAssets",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(TaroServer).ListAssets(ctx, req.(*ListAssetRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _Taro_StopDaemon_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(StopRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(TaroServer).StopDaemon(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/tarorpc.Taro/StopDaemon",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(TaroServer).StopDaemon(ctx, req.(*StopRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _Taro_DebugLevel_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(DebugLevelRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(TaroServer).DebugLevel(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/tarorpc.Taro/DebugLevel",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(TaroServer).DebugLevel(ctx, req.(*DebugLevelRequest))
	}
	return interceptor(ctx, in, info, handler)
}

// Taro_ServiceDesc is the grpc.ServiceDesc for Taro service.
// It's only intended for direct use with grpc.RegisterService,
// and not to be introspected or modified (even as a copy)
var Taro_ServiceDesc = grpc.ServiceDesc{
	ServiceName: "tarorpc.Taro",
	HandlerType: (*TaroServer)(nil),
	Methods: []grpc.MethodDesc{
		{
			MethodName: "MintAsset",
			Handler:    _Taro_MintAsset_Handler,
		},
		{
			MethodName: "ListAssets",
			Handler:    _Taro_ListAssets_Handler,
		},
		{
			MethodName: "StopDaemon",
			Handler:    _Taro_StopDaemon_Handler,
		},
		{
			MethodName: "DebugLevel",
			Handler:    _Taro_DebugLevel_Handler,
		},
	},
	Streams:  []grpc.StreamDesc{},
	Metadata: "taro.proto",
}
