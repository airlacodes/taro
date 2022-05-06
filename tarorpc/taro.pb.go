// Code generated by protoc-gen-go. DO NOT EDIT.
// versions:
// 	protoc-gen-go v1.26.0
// 	protoc        v3.6.1
// source: taro.proto

package tarorpc

import (
	protoreflect "google.golang.org/protobuf/reflect/protoreflect"
	protoimpl "google.golang.org/protobuf/runtime/protoimpl"
	reflect "reflect"
	sync "sync"
)

const (
	// Verify that this generated code is sufficiently up-to-date.
	_ = protoimpl.EnforceVersion(20 - protoimpl.MinVersion)
	// Verify that runtime/protoimpl is sufficiently up-to-date.
	_ = protoimpl.EnforceVersion(protoimpl.MaxVersion - 20)
)

type MintAssetRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *MintAssetRequest) Reset() {
	*x = MintAssetRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_taro_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MintAssetRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MintAssetRequest) ProtoMessage() {}

func (x *MintAssetRequest) ProtoReflect() protoreflect.Message {
	mi := &file_taro_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MintAssetRequest.ProtoReflect.Descriptor instead.
func (*MintAssetRequest) Descriptor() ([]byte, []int) {
	return file_taro_proto_rawDescGZIP(), []int{0}
}

type MintAssetResponse struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *MintAssetResponse) Reset() {
	*x = MintAssetResponse{}
	if protoimpl.UnsafeEnabled {
		mi := &file_taro_proto_msgTypes[1]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MintAssetResponse) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MintAssetResponse) ProtoMessage() {}

func (x *MintAssetResponse) ProtoReflect() protoreflect.Message {
	mi := &file_taro_proto_msgTypes[1]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MintAssetResponse.ProtoReflect.Descriptor instead.
func (*MintAssetResponse) Descriptor() ([]byte, []int) {
	return file_taro_proto_rawDescGZIP(), []int{1}
}

type ListAssetRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *ListAssetRequest) Reset() {
	*x = ListAssetRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_taro_proto_msgTypes[2]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ListAssetRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ListAssetRequest) ProtoMessage() {}

func (x *ListAssetRequest) ProtoReflect() protoreflect.Message {
	mi := &file_taro_proto_msgTypes[2]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ListAssetRequest.ProtoReflect.Descriptor instead.
func (*ListAssetRequest) Descriptor() ([]byte, []int) {
	return file_taro_proto_rawDescGZIP(), []int{2}
}

type ListAssetResponse struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *ListAssetResponse) Reset() {
	*x = ListAssetResponse{}
	if protoimpl.UnsafeEnabled {
		mi := &file_taro_proto_msgTypes[3]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ListAssetResponse) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ListAssetResponse) ProtoMessage() {}

func (x *ListAssetResponse) ProtoReflect() protoreflect.Message {
	mi := &file_taro_proto_msgTypes[3]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ListAssetResponse.ProtoReflect.Descriptor instead.
func (*ListAssetResponse) Descriptor() ([]byte, []int) {
	return file_taro_proto_rawDescGZIP(), []int{3}
}

type StopRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *StopRequest) Reset() {
	*x = StopRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_taro_proto_msgTypes[4]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *StopRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*StopRequest) ProtoMessage() {}

func (x *StopRequest) ProtoReflect() protoreflect.Message {
	mi := &file_taro_proto_msgTypes[4]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use StopRequest.ProtoReflect.Descriptor instead.
func (*StopRequest) Descriptor() ([]byte, []int) {
	return file_taro_proto_rawDescGZIP(), []int{4}
}

type StopResponse struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *StopResponse) Reset() {
	*x = StopResponse{}
	if protoimpl.UnsafeEnabled {
		mi := &file_taro_proto_msgTypes[5]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *StopResponse) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*StopResponse) ProtoMessage() {}

func (x *StopResponse) ProtoReflect() protoreflect.Message {
	mi := &file_taro_proto_msgTypes[5]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use StopResponse.ProtoReflect.Descriptor instead.
func (*StopResponse) Descriptor() ([]byte, []int) {
	return file_taro_proto_rawDescGZIP(), []int{5}
}

type DebugLevelRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	Show      bool   `protobuf:"varint,1,opt,name=show,proto3" json:"show,omitempty"`
	LevelSpec string `protobuf:"bytes,2,opt,name=level_spec,json=levelSpec,proto3" json:"level_spec,omitempty"`
}

func (x *DebugLevelRequest) Reset() {
	*x = DebugLevelRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_taro_proto_msgTypes[6]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *DebugLevelRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*DebugLevelRequest) ProtoMessage() {}

func (x *DebugLevelRequest) ProtoReflect() protoreflect.Message {
	mi := &file_taro_proto_msgTypes[6]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use DebugLevelRequest.ProtoReflect.Descriptor instead.
func (*DebugLevelRequest) Descriptor() ([]byte, []int) {
	return file_taro_proto_rawDescGZIP(), []int{6}
}

func (x *DebugLevelRequest) GetShow() bool {
	if x != nil {
		return x.Show
	}
	return false
}

func (x *DebugLevelRequest) GetLevelSpec() string {
	if x != nil {
		return x.LevelSpec
	}
	return ""
}

type DebugLevelResponse struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	SubSystems string `protobuf:"bytes,1,opt,name=sub_systems,json=subSystems,proto3" json:"sub_systems,omitempty"`
}

func (x *DebugLevelResponse) Reset() {
	*x = DebugLevelResponse{}
	if protoimpl.UnsafeEnabled {
		mi := &file_taro_proto_msgTypes[7]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *DebugLevelResponse) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*DebugLevelResponse) ProtoMessage() {}

func (x *DebugLevelResponse) ProtoReflect() protoreflect.Message {
	mi := &file_taro_proto_msgTypes[7]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use DebugLevelResponse.ProtoReflect.Descriptor instead.
func (*DebugLevelResponse) Descriptor() ([]byte, []int) {
	return file_taro_proto_rawDescGZIP(), []int{7}
}

func (x *DebugLevelResponse) GetSubSystems() string {
	if x != nil {
		return x.SubSystems
	}
	return ""
}

var File_taro_proto protoreflect.FileDescriptor

var file_taro_proto_rawDesc = []byte{
	0x0a, 0x0a, 0x74, 0x61, 0x72, 0x6f, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12, 0x07, 0x74, 0x61,
	0x72, 0x6f, 0x72, 0x70, 0x63, 0x22, 0x12, 0x0a, 0x10, 0x4d, 0x69, 0x6e, 0x74, 0x41, 0x73, 0x73,
	0x65, 0x74, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x22, 0x13, 0x0a, 0x11, 0x4d, 0x69, 0x6e,
	0x74, 0x41, 0x73, 0x73, 0x65, 0x74, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x22, 0x12,
	0x0a, 0x10, 0x4c, 0x69, 0x73, 0x74, 0x41, 0x73, 0x73, 0x65, 0x74, 0x52, 0x65, 0x71, 0x75, 0x65,
	0x73, 0x74, 0x22, 0x13, 0x0a, 0x11, 0x4c, 0x69, 0x73, 0x74, 0x41, 0x73, 0x73, 0x65, 0x74, 0x52,
	0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x22, 0x0d, 0x0a, 0x0b, 0x53, 0x74, 0x6f, 0x70, 0x52,
	0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x22, 0x0e, 0x0a, 0x0c, 0x53, 0x74, 0x6f, 0x70, 0x52, 0x65,
	0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x22, 0x46, 0x0a, 0x11, 0x44, 0x65, 0x62, 0x75, 0x67, 0x4c,
	0x65, 0x76, 0x65, 0x6c, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x12, 0x12, 0x0a, 0x04, 0x73,
	0x68, 0x6f, 0x77, 0x18, 0x01, 0x20, 0x01, 0x28, 0x08, 0x52, 0x04, 0x73, 0x68, 0x6f, 0x77, 0x12,
	0x1d, 0x0a, 0x0a, 0x6c, 0x65, 0x76, 0x65, 0x6c, 0x5f, 0x73, 0x70, 0x65, 0x63, 0x18, 0x02, 0x20,
	0x01, 0x28, 0x09, 0x52, 0x09, 0x6c, 0x65, 0x76, 0x65, 0x6c, 0x53, 0x70, 0x65, 0x63, 0x22, 0x35,
	0x0a, 0x12, 0x44, 0x65, 0x62, 0x75, 0x67, 0x4c, 0x65, 0x76, 0x65, 0x6c, 0x52, 0x65, 0x73, 0x70,
	0x6f, 0x6e, 0x73, 0x65, 0x12, 0x1f, 0x0a, 0x0b, 0x73, 0x75, 0x62, 0x5f, 0x73, 0x79, 0x73, 0x74,
	0x65, 0x6d, 0x73, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x0a, 0x73, 0x75, 0x62, 0x53, 0x79,
	0x73, 0x74, 0x65, 0x6d, 0x73, 0x32, 0x91, 0x02, 0x0a, 0x04, 0x54, 0x61, 0x72, 0x6f, 0x12, 0x42,
	0x0a, 0x09, 0x4d, 0x69, 0x6e, 0x74, 0x41, 0x73, 0x73, 0x65, 0x74, 0x12, 0x19, 0x2e, 0x74, 0x61,
	0x72, 0x6f, 0x72, 0x70, 0x63, 0x2e, 0x4d, 0x69, 0x6e, 0x74, 0x41, 0x73, 0x73, 0x65, 0x74, 0x52,
	0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x1a, 0x1a, 0x2e, 0x74, 0x61, 0x72, 0x6f, 0x72, 0x70, 0x63,
	0x2e, 0x4d, 0x69, 0x6e, 0x74, 0x41, 0x73, 0x73, 0x65, 0x74, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e,
	0x73, 0x65, 0x12, 0x43, 0x0a, 0x0a, 0x4c, 0x69, 0x73, 0x74, 0x41, 0x73, 0x73, 0x65, 0x74, 0x73,
	0x12, 0x19, 0x2e, 0x74, 0x61, 0x72, 0x6f, 0x72, 0x70, 0x63, 0x2e, 0x4c, 0x69, 0x73, 0x74, 0x41,
	0x73, 0x73, 0x65, 0x74, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x1a, 0x1a, 0x2e, 0x74, 0x61,
	0x72, 0x6f, 0x72, 0x70, 0x63, 0x2e, 0x4c, 0x69, 0x73, 0x74, 0x41, 0x73, 0x73, 0x65, 0x74, 0x52,
	0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x12, 0x39, 0x0a, 0x0a, 0x53, 0x74, 0x6f, 0x70, 0x44,
	0x61, 0x65, 0x6d, 0x6f, 0x6e, 0x12, 0x14, 0x2e, 0x74, 0x61, 0x72, 0x6f, 0x72, 0x70, 0x63, 0x2e,
	0x53, 0x74, 0x6f, 0x70, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x1a, 0x15, 0x2e, 0x74, 0x61,
	0x72, 0x6f, 0x72, 0x70, 0x63, 0x2e, 0x53, 0x74, 0x6f, 0x70, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e,
	0x73, 0x65, 0x12, 0x45, 0x0a, 0x0a, 0x44, 0x65, 0x62, 0x75, 0x67, 0x4c, 0x65, 0x76, 0x65, 0x6c,
	0x12, 0x1a, 0x2e, 0x74, 0x61, 0x72, 0x6f, 0x72, 0x70, 0x63, 0x2e, 0x44, 0x65, 0x62, 0x75, 0x67,
	0x4c, 0x65, 0x76, 0x65, 0x6c, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x1a, 0x1b, 0x2e, 0x74,
	0x61, 0x72, 0x6f, 0x72, 0x70, 0x63, 0x2e, 0x44, 0x65, 0x62, 0x75, 0x67, 0x4c, 0x65, 0x76, 0x65,
	0x6c, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x42, 0x22, 0x5a, 0x20, 0x67, 0x69, 0x74,
	0x68, 0x75, 0x62, 0x2e, 0x63, 0x6f, 0x6d, 0x2f, 0x6c, 0x69, 0x67, 0x68, 0x74, 0x6e, 0x69, 0x6e,
	0x67, 0x6c, 0x61, 0x62, 0x73, 0x2f, 0x74, 0x61, 0x72, 0x6f, 0x72, 0x70, 0x63, 0x62, 0x06, 0x70,
	0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_taro_proto_rawDescOnce sync.Once
	file_taro_proto_rawDescData = file_taro_proto_rawDesc
)

func file_taro_proto_rawDescGZIP() []byte {
	file_taro_proto_rawDescOnce.Do(func() {
		file_taro_proto_rawDescData = protoimpl.X.CompressGZIP(file_taro_proto_rawDescData)
	})
	return file_taro_proto_rawDescData
}

var file_taro_proto_msgTypes = make([]protoimpl.MessageInfo, 8)
var file_taro_proto_goTypes = []interface{}{
	(*MintAssetRequest)(nil),   // 0: tarorpc.MintAssetRequest
	(*MintAssetResponse)(nil),  // 1: tarorpc.MintAssetResponse
	(*ListAssetRequest)(nil),   // 2: tarorpc.ListAssetRequest
	(*ListAssetResponse)(nil),  // 3: tarorpc.ListAssetResponse
	(*StopRequest)(nil),        // 4: tarorpc.StopRequest
	(*StopResponse)(nil),       // 5: tarorpc.StopResponse
	(*DebugLevelRequest)(nil),  // 6: tarorpc.DebugLevelRequest
	(*DebugLevelResponse)(nil), // 7: tarorpc.DebugLevelResponse
}
var file_taro_proto_depIdxs = []int32{
	0, // 0: tarorpc.Taro.MintAsset:input_type -> tarorpc.MintAssetRequest
	2, // 1: tarorpc.Taro.ListAssets:input_type -> tarorpc.ListAssetRequest
	4, // 2: tarorpc.Taro.StopDaemon:input_type -> tarorpc.StopRequest
	6, // 3: tarorpc.Taro.DebugLevel:input_type -> tarorpc.DebugLevelRequest
	1, // 4: tarorpc.Taro.MintAsset:output_type -> tarorpc.MintAssetResponse
	3, // 5: tarorpc.Taro.ListAssets:output_type -> tarorpc.ListAssetResponse
	5, // 6: tarorpc.Taro.StopDaemon:output_type -> tarorpc.StopResponse
	7, // 7: tarorpc.Taro.DebugLevel:output_type -> tarorpc.DebugLevelResponse
	4, // [4:8] is the sub-list for method output_type
	0, // [0:4] is the sub-list for method input_type
	0, // [0:0] is the sub-list for extension type_name
	0, // [0:0] is the sub-list for extension extendee
	0, // [0:0] is the sub-list for field type_name
}

func init() { file_taro_proto_init() }
func file_taro_proto_init() {
	if File_taro_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_taro_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MintAssetRequest); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_taro_proto_msgTypes[1].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MintAssetResponse); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_taro_proto_msgTypes[2].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ListAssetRequest); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_taro_proto_msgTypes[3].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ListAssetResponse); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_taro_proto_msgTypes[4].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*StopRequest); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_taro_proto_msgTypes[5].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*StopResponse); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_taro_proto_msgTypes[6].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*DebugLevelRequest); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_taro_proto_msgTypes[7].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*DebugLevelResponse); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
	}
	type x struct{}
	out := protoimpl.TypeBuilder{
		File: protoimpl.DescBuilder{
			GoPackagePath: reflect.TypeOf(x{}).PkgPath(),
			RawDescriptor: file_taro_proto_rawDesc,
			NumEnums:      0,
			NumMessages:   8,
			NumExtensions: 0,
			NumServices:   1,
		},
		GoTypes:           file_taro_proto_goTypes,
		DependencyIndexes: file_taro_proto_depIdxs,
		MessageInfos:      file_taro_proto_msgTypes,
	}.Build()
	File_taro_proto = out.File
	file_taro_proto_rawDesc = nil
	file_taro_proto_goTypes = nil
	file_taro_proto_depIdxs = nil
}
