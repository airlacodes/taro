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
	// tarocli: `assets mint`
	//MintAsset will attempts to mint the set of assets (async by default to
	//ensure proper batching) specified in the request.
	MintAsset(ctx context.Context, in *MintAssetRequest, opts ...grpc.CallOption) (*MintAssetResponse, error)
	// tarocli: `assets list`
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
	// tarocli: `addrs query`
	//QueryTaroAddrs queries the set of Taro addresses stored in the database.
	QueryAddrs(ctx context.Context, in *QueryAddrRequest, opts ...grpc.CallOption) (*QueryAddrResponse, error)
	// tarocli: `addrs new`
	//NewAddr makes a new address from the set of request params.
	NewAddr(ctx context.Context, in *NewAddrRequest, opts ...grpc.CallOption) (*Addr, error)
	// tarocli: `addrs decode`
	//DecodeAddr decode a Taro address into a partial asset message that
	//represents the asset it wants to receive.
	DecodeAddr(ctx context.Context, in *DecodeAddrRequest, opts ...grpc.CallOption) (*Addr, error)
	// tarocli: `proofs verify`
	//VerifyProof attempts to verify a given proof file that claims to be anchored
	//at the specified genesis point.
	VerifyProof(ctx context.Context, in *ProofFile, opts ...grpc.CallOption) (*ProofVerifyResponse, error)
	// tarocli: `proofs export`
	//ExportProof exports the latest raw proof file anchored at the specified
	//script_key.
	ExportProof(ctx context.Context, in *ExportProofRequest, opts ...grpc.CallOption) (*ProofFile, error)
	// tarocli: `proofs import`
	//ImportProof attempts to import a proof file into the daemon. If successful,
	//a new asset will be inserted on disk, spendable using the specified target
	//script key, and internal key.
	ImportProof(ctx context.Context, in *ImportProofRequest, opts ...grpc.CallOption) (*ImportProofResponse, error)
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

func (c *taroClient) QueryAddrs(ctx context.Context, in *QueryAddrRequest, opts ...grpc.CallOption) (*QueryAddrResponse, error) {
	out := new(QueryAddrResponse)
	err := c.cc.Invoke(ctx, "/tarorpc.Taro/QueryAddrs", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *taroClient) NewAddr(ctx context.Context, in *NewAddrRequest, opts ...grpc.CallOption) (*Addr, error) {
	out := new(Addr)
	err := c.cc.Invoke(ctx, "/tarorpc.Taro/NewAddr", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *taroClient) DecodeAddr(ctx context.Context, in *DecodeAddrRequest, opts ...grpc.CallOption) (*Addr, error) {
	out := new(Addr)
	err := c.cc.Invoke(ctx, "/tarorpc.Taro/DecodeAddr", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *taroClient) VerifyProof(ctx context.Context, in *ProofFile, opts ...grpc.CallOption) (*ProofVerifyResponse, error) {
	out := new(ProofVerifyResponse)
	err := c.cc.Invoke(ctx, "/tarorpc.Taro/VerifyProof", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *taroClient) ExportProof(ctx context.Context, in *ExportProofRequest, opts ...grpc.CallOption) (*ProofFile, error) {
	out := new(ProofFile)
	err := c.cc.Invoke(ctx, "/tarorpc.Taro/ExportProof", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *taroClient) ImportProof(ctx context.Context, in *ImportProofRequest, opts ...grpc.CallOption) (*ImportProofResponse, error) {
	out := new(ImportProofResponse)
	err := c.cc.Invoke(ctx, "/tarorpc.Taro/ImportProof", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

// TaroServer is the server API for Taro service.
// All implementations must embed UnimplementedTaroServer
// for forward compatibility
type TaroServer interface {
	// tarocli: `assets mint`
	//MintAsset will attempts to mint the set of assets (async by default to
	//ensure proper batching) specified in the request.
	MintAsset(context.Context, *MintAssetRequest) (*MintAssetResponse, error)
	// tarocli: `assets list`
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
	// tarocli: `addrs query`
	//QueryTaroAddrs queries the set of Taro addresses stored in the database.
	QueryAddrs(context.Context, *QueryAddrRequest) (*QueryAddrResponse, error)
	// tarocli: `addrs new`
	//NewAddr makes a new address from the set of request params.
	NewAddr(context.Context, *NewAddrRequest) (*Addr, error)
	// tarocli: `addrs decode`
	//DecodeAddr decode a Taro address into a partial asset message that
	//represents the asset it wants to receive.
	DecodeAddr(context.Context, *DecodeAddrRequest) (*Addr, error)
	// tarocli: `proofs verify`
	//VerifyProof attempts to verify a given proof file that claims to be anchored
	//at the specified genesis point.
	VerifyProof(context.Context, *ProofFile) (*ProofVerifyResponse, error)
	// tarocli: `proofs export`
	//ExportProof exports the latest raw proof file anchored at the specified
	//script_key.
	ExportProof(context.Context, *ExportProofRequest) (*ProofFile, error)
	// tarocli: `proofs import`
	//ImportProof attempts to import a proof file into the daemon. If successful,
	//a new asset will be inserted on disk, spendable using the specified target
	//script key, and internal key.
	ImportProof(context.Context, *ImportProofRequest) (*ImportProofResponse, error)
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
func (UnimplementedTaroServer) QueryAddrs(context.Context, *QueryAddrRequest) (*QueryAddrResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method QueryAddrs not implemented")
}
func (UnimplementedTaroServer) NewAddr(context.Context, *NewAddrRequest) (*Addr, error) {
	return nil, status.Errorf(codes.Unimplemented, "method NewAddr not implemented")
}
func (UnimplementedTaroServer) DecodeAddr(context.Context, *DecodeAddrRequest) (*Addr, error) {
	return nil, status.Errorf(codes.Unimplemented, "method DecodeAddr not implemented")
}
func (UnimplementedTaroServer) VerifyProof(context.Context, *ProofFile) (*ProofVerifyResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method VerifyProof not implemented")
}
func (UnimplementedTaroServer) ExportProof(context.Context, *ExportProofRequest) (*ProofFile, error) {
	return nil, status.Errorf(codes.Unimplemented, "method ExportProof not implemented")
}
func (UnimplementedTaroServer) ImportProof(context.Context, *ImportProofRequest) (*ImportProofResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method ImportProof not implemented")
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

func _Taro_QueryAddrs_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(QueryAddrRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(TaroServer).QueryAddrs(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/tarorpc.Taro/QueryAddrs",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(TaroServer).QueryAddrs(ctx, req.(*QueryAddrRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _Taro_NewAddr_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(NewAddrRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(TaroServer).NewAddr(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/tarorpc.Taro/NewAddr",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(TaroServer).NewAddr(ctx, req.(*NewAddrRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _Taro_DecodeAddr_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(DecodeAddrRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(TaroServer).DecodeAddr(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/tarorpc.Taro/DecodeAddr",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(TaroServer).DecodeAddr(ctx, req.(*DecodeAddrRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _Taro_VerifyProof_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(ProofFile)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(TaroServer).VerifyProof(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/tarorpc.Taro/VerifyProof",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(TaroServer).VerifyProof(ctx, req.(*ProofFile))
	}
	return interceptor(ctx, in, info, handler)
}

func _Taro_ExportProof_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(ExportProofRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(TaroServer).ExportProof(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/tarorpc.Taro/ExportProof",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(TaroServer).ExportProof(ctx, req.(*ExportProofRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _Taro_ImportProof_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(ImportProofRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(TaroServer).ImportProof(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/tarorpc.Taro/ImportProof",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(TaroServer).ImportProof(ctx, req.(*ImportProofRequest))
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
		{
			MethodName: "QueryAddrs",
			Handler:    _Taro_QueryAddrs_Handler,
		},
		{
			MethodName: "NewAddr",
			Handler:    _Taro_NewAddr_Handler,
		},
		{
			MethodName: "DecodeAddr",
			Handler:    _Taro_DecodeAddr_Handler,
		},
		{
			MethodName: "VerifyProof",
			Handler:    _Taro_VerifyProof_Handler,
		},
		{
			MethodName: "ExportProof",
			Handler:    _Taro_ExportProof_Handler,
		},
		{
			MethodName: "ImportProof",
			Handler:    _Taro_ImportProof_Handler,
		},
	},
	Streams:  []grpc.StreamDesc{},
	Metadata: "taro.proto",
}
