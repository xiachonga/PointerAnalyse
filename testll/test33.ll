; ModuleID = '../test33.c'
source_filename = "../test33.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.fptr = type { i32 (i32, i32)* }
%struct.wfsptr = type { %struct.fsptr* }
%struct.fsptr = type { %struct.fptr* }

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @plus(i32 %a, i32 %b) #0 !dbg !7 {
entry:
  %a.addr = alloca i32, align 4
  %b.addr = alloca i32, align 4
  store i32 %a, i32* %a.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %a.addr, metadata !11, metadata !DIExpression()), !dbg !12
  store i32 %b, i32* %b.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %b.addr, metadata !13, metadata !DIExpression()), !dbg !14
  %0 = load i32, i32* %a.addr, align 4, !dbg !15
  %1 = load i32, i32* %b.addr, align 4, !dbg !16
  %add = add nsw i32 %0, %1, !dbg !17
  ret i32 %add, !dbg !18
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @minus(i32 %a, i32 %b) #0 !dbg !19 {
entry:
  %a.addr = alloca i32, align 4
  %b.addr = alloca i32, align 4
  store i32 %a, i32* %a.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %a.addr, metadata !20, metadata !DIExpression()), !dbg !21
  store i32 %b, i32* %b.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %b.addr, metadata !22, metadata !DIExpression()), !dbg !23
  %0 = load i32, i32* %a.addr, align 4, !dbg !24
  %1 = load i32, i32* %b.addr, align 4, !dbg !25
  %sub = sub nsw i32 %0, %1, !dbg !26
  ret i32 %sub, !dbg !27
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local %struct.fptr* @foo(i32 %a, i32 %b, %struct.wfsptr* %a_fptr, %struct.wfsptr* %b_fptr) #0 !dbg !28 {
entry:
  %retval = alloca %struct.fptr*, align 8
  %a.addr = alloca i32, align 4
  %b.addr = alloca i32, align 4
  %a_fptr.addr = alloca %struct.wfsptr*, align 8
  %b_fptr.addr = alloca %struct.wfsptr*, align 8
  %temp = alloca %struct.fsptr*, align 8
  store i32 %a, i32* %a.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %a.addr, metadata !44, metadata !DIExpression()), !dbg !45
  store i32 %b, i32* %b.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %b.addr, metadata !46, metadata !DIExpression()), !dbg !47
  store %struct.wfsptr* %a_fptr, %struct.wfsptr** %a_fptr.addr, align 8
  call void @llvm.dbg.declare(metadata %struct.wfsptr** %a_fptr.addr, metadata !48, metadata !DIExpression()), !dbg !49
  store %struct.wfsptr* %b_fptr, %struct.wfsptr** %b_fptr.addr, align 8
  call void @llvm.dbg.declare(metadata %struct.wfsptr** %b_fptr.addr, metadata !50, metadata !DIExpression()), !dbg !51
  %0 = load i32, i32* %a.addr, align 4, !dbg !52
  %cmp = icmp sgt i32 %0, 0, !dbg !54
  br i1 %cmp, label %land.lhs.true, label %if.end, !dbg !55

land.lhs.true:                                    ; preds = %entry
  %1 = load i32, i32* %b.addr, align 4, !dbg !56
  %cmp1 = icmp slt i32 %1, 0, !dbg !57
  br i1 %cmp1, label %if.then, label %if.end, !dbg !58

if.then:                                          ; preds = %land.lhs.true
  call void @llvm.dbg.declare(metadata %struct.fsptr** %temp, metadata !59, metadata !DIExpression()), !dbg !61
  %2 = load %struct.wfsptr*, %struct.wfsptr** %a_fptr.addr, align 8, !dbg !62
  %wfptr = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %2, i32 0, i32 0, !dbg !63
  %3 = load %struct.fsptr*, %struct.fsptr** %wfptr, align 8, !dbg !63
  store %struct.fsptr* %3, %struct.fsptr** %temp, align 8, !dbg !61
  %4 = load %struct.wfsptr*, %struct.wfsptr** %b_fptr.addr, align 8, !dbg !64
  %wfptr2 = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %4, i32 0, i32 0, !dbg !65
  %5 = load %struct.fsptr*, %struct.fsptr** %wfptr2, align 8, !dbg !65
  %sptr = getelementptr inbounds %struct.fsptr, %struct.fsptr* %5, i32 0, i32 0, !dbg !66
  %6 = load %struct.fptr*, %struct.fptr** %sptr, align 8, !dbg !66
  %7 = load %struct.wfsptr*, %struct.wfsptr** %a_fptr.addr, align 8, !dbg !67
  %wfptr3 = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %7, i32 0, i32 0, !dbg !68
  %8 = load %struct.fsptr*, %struct.fsptr** %wfptr3, align 8, !dbg !68
  %sptr4 = getelementptr inbounds %struct.fsptr, %struct.fsptr* %8, i32 0, i32 0, !dbg !69
  store %struct.fptr* %6, %struct.fptr** %sptr4, align 8, !dbg !70
  %9 = load %struct.fsptr*, %struct.fsptr** %temp, align 8, !dbg !71
  %sptr5 = getelementptr inbounds %struct.fsptr, %struct.fsptr* %9, i32 0, i32 0, !dbg !72
  %10 = load %struct.fptr*, %struct.fptr** %sptr5, align 8, !dbg !72
  %11 = load %struct.wfsptr*, %struct.wfsptr** %b_fptr.addr, align 8, !dbg !73
  %wfptr6 = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %11, i32 0, i32 0, !dbg !74
  %12 = load %struct.fsptr*, %struct.fsptr** %wfptr6, align 8, !dbg !74
  %sptr7 = getelementptr inbounds %struct.fsptr, %struct.fsptr* %12, i32 0, i32 0, !dbg !75
  store %struct.fptr* %10, %struct.fptr** %sptr7, align 8, !dbg !76
  %13 = load %struct.wfsptr*, %struct.wfsptr** %a_fptr.addr, align 8, !dbg !77
  %wfptr8 = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %13, i32 0, i32 0, !dbg !78
  %14 = load %struct.fsptr*, %struct.fsptr** %wfptr8, align 8, !dbg !78
  %sptr9 = getelementptr inbounds %struct.fsptr, %struct.fsptr* %14, i32 0, i32 0, !dbg !79
  %15 = load %struct.fptr*, %struct.fptr** %sptr9, align 8, !dbg !79
  %p_fptr = getelementptr inbounds %struct.fptr, %struct.fptr* %15, i32 0, i32 0, !dbg !80
  %16 = load i32 (i32, i32)*, i32 (i32, i32)** %p_fptr, align 8, !dbg !80
  %17 = load i32, i32* %a.addr, align 4, !dbg !81
  %18 = load i32, i32* %b.addr, align 4, !dbg !82
  %call = call i32 %16(i32 %17, i32 %18), !dbg !77
  %19 = load %struct.wfsptr*, %struct.wfsptr** %a_fptr.addr, align 8, !dbg !83
  %wfptr10 = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %19, i32 0, i32 0, !dbg !84
  %20 = load %struct.fsptr*, %struct.fsptr** %wfptr10, align 8, !dbg !84
  %sptr11 = getelementptr inbounds %struct.fsptr, %struct.fsptr* %20, i32 0, i32 0, !dbg !85
  %21 = load %struct.fptr*, %struct.fptr** %sptr11, align 8, !dbg !85
  store %struct.fptr* %21, %struct.fptr** %retval, align 8, !dbg !86
  br label %return, !dbg !86

if.end:                                           ; preds = %land.lhs.true, %entry
  %22 = load %struct.wfsptr*, %struct.wfsptr** %b_fptr.addr, align 8, !dbg !87
  %wfptr12 = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %22, i32 0, i32 0, !dbg !88
  %23 = load %struct.fsptr*, %struct.fsptr** %wfptr12, align 8, !dbg !88
  %sptr13 = getelementptr inbounds %struct.fsptr, %struct.fsptr* %23, i32 0, i32 0, !dbg !89
  %24 = load %struct.fptr*, %struct.fptr** %sptr13, align 8, !dbg !89
  store %struct.fptr* %24, %struct.fptr** %retval, align 8, !dbg !90
  br label %return, !dbg !90

return:                                           ; preds = %if.end, %if.then
  %25 = load %struct.fptr*, %struct.fptr** %retval, align 8, !dbg !91
  ret %struct.fptr* %25, !dbg !91
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local %struct.fptr* @clever(i32 %a, i32 %b, %struct.fsptr* %a_fptr, %struct.fsptr* %b_fptr) #0 !dbg !92 {
entry:
  %a.addr = alloca i32, align 4
  %b.addr = alloca i32, align 4
  %a_fptr.addr = alloca %struct.fsptr*, align 8
  %b_fptr.addr = alloca %struct.fsptr*, align 8
  %t1_fptr = alloca %struct.wfsptr, align 8
  %t2_fptr = alloca %struct.wfsptr, align 8
  store i32 %a, i32* %a.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %a.addr, metadata !95, metadata !DIExpression()), !dbg !96
  store i32 %b, i32* %b.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %b.addr, metadata !97, metadata !DIExpression()), !dbg !98
  store %struct.fsptr* %a_fptr, %struct.fsptr** %a_fptr.addr, align 8
  call void @llvm.dbg.declare(metadata %struct.fsptr** %a_fptr.addr, metadata !99, metadata !DIExpression()), !dbg !100
  store %struct.fsptr* %b_fptr, %struct.fsptr** %b_fptr.addr, align 8
  call void @llvm.dbg.declare(metadata %struct.fsptr** %b_fptr.addr, metadata !101, metadata !DIExpression()), !dbg !102
  call void @llvm.dbg.declare(metadata %struct.wfsptr* %t1_fptr, metadata !103, metadata !DIExpression()), !dbg !104
  %0 = load %struct.fsptr*, %struct.fsptr** %a_fptr.addr, align 8, !dbg !105
  %wfptr = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %t1_fptr, i32 0, i32 0, !dbg !106
  store %struct.fsptr* %0, %struct.fsptr** %wfptr, align 8, !dbg !107
  call void @llvm.dbg.declare(metadata %struct.wfsptr* %t2_fptr, metadata !108, metadata !DIExpression()), !dbg !109
  %1 = load %struct.fsptr*, %struct.fsptr** %b_fptr.addr, align 8, !dbg !110
  %wfptr1 = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %t2_fptr, i32 0, i32 0, !dbg !111
  store %struct.fsptr* %1, %struct.fsptr** %wfptr1, align 8, !dbg !112
  %2 = load i32, i32* %a.addr, align 4, !dbg !113
  %3 = load i32, i32* %b.addr, align 4, !dbg !114
  %call = call %struct.fptr* @foo(i32 %2, i32 %3, %struct.wfsptr* %t1_fptr, %struct.wfsptr* %t2_fptr), !dbg !115
  ret %struct.fptr* %call, !dbg !116
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @make_simple_alias(%struct.wfsptr* %a_fptr, %struct.fsptr* %b_fptr) #0 !dbg !117 {
entry:
  %a_fptr.addr = alloca %struct.wfsptr*, align 8
  %b_fptr.addr = alloca %struct.fsptr*, align 8
  store %struct.wfsptr* %a_fptr, %struct.wfsptr** %a_fptr.addr, align 8
  call void @llvm.dbg.declare(metadata %struct.wfsptr** %a_fptr.addr, metadata !120, metadata !DIExpression()), !dbg !121
  store %struct.fsptr* %b_fptr, %struct.fsptr** %b_fptr.addr, align 8
  call void @llvm.dbg.declare(metadata %struct.fsptr** %b_fptr.addr, metadata !122, metadata !DIExpression()), !dbg !123
  %0 = load %struct.fsptr*, %struct.fsptr** %b_fptr.addr, align 8, !dbg !124
  %1 = load %struct.wfsptr*, %struct.wfsptr** %a_fptr.addr, align 8, !dbg !125
  %wfptr = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %1, i32 0, i32 0, !dbg !126
  store %struct.fsptr* %0, %struct.fsptr** %wfptr, align 8, !dbg !127
  ret void, !dbg !128
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @make_alias(%struct.wfsptr* %a_fptr, %struct.wfsptr* %b_fptr) #0 !dbg !129 {
entry:
  %a_fptr.addr = alloca %struct.wfsptr*, align 8
  %b_fptr.addr = alloca %struct.wfsptr*, align 8
  store %struct.wfsptr* %a_fptr, %struct.wfsptr** %a_fptr.addr, align 8
  call void @llvm.dbg.declare(metadata %struct.wfsptr** %a_fptr.addr, metadata !132, metadata !DIExpression()), !dbg !133
  store %struct.wfsptr* %b_fptr, %struct.wfsptr** %b_fptr.addr, align 8
  call void @llvm.dbg.declare(metadata %struct.wfsptr** %b_fptr.addr, metadata !134, metadata !DIExpression()), !dbg !135
  %0 = load %struct.wfsptr*, %struct.wfsptr** %b_fptr.addr, align 8, !dbg !136
  %wfptr = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %0, i32 0, i32 0, !dbg !137
  %1 = load %struct.fsptr*, %struct.fsptr** %wfptr, align 8, !dbg !137
  %sptr = getelementptr inbounds %struct.fsptr, %struct.fsptr* %1, i32 0, i32 0, !dbg !138
  %2 = load %struct.fptr*, %struct.fptr** %sptr, align 8, !dbg !138
  %3 = load %struct.wfsptr*, %struct.wfsptr** %a_fptr.addr, align 8, !dbg !139
  %wfptr1 = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %3, i32 0, i32 0, !dbg !140
  %4 = load %struct.fsptr*, %struct.fsptr** %wfptr1, align 8, !dbg !140
  %sptr2 = getelementptr inbounds %struct.fsptr, %struct.fsptr* %4, i32 0, i32 0, !dbg !141
  store %struct.fptr* %2, %struct.fptr** %sptr2, align 8, !dbg !142
  ret void, !dbg !143
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @swap_w(%struct.wfsptr* %a_fptr, %struct.wfsptr* %b_fptr) #0 !dbg !144 {
entry:
  %a_fptr.addr = alloca %struct.wfsptr*, align 8
  %b_fptr.addr = alloca %struct.wfsptr*, align 8
  %wftemp = alloca %struct.wfsptr, align 8
  store %struct.wfsptr* %a_fptr, %struct.wfsptr** %a_fptr.addr, align 8
  call void @llvm.dbg.declare(metadata %struct.wfsptr** %a_fptr.addr, metadata !145, metadata !DIExpression()), !dbg !146
  store %struct.wfsptr* %b_fptr, %struct.wfsptr** %b_fptr.addr, align 8
  call void @llvm.dbg.declare(metadata %struct.wfsptr** %b_fptr.addr, metadata !147, metadata !DIExpression()), !dbg !148
  call void @llvm.dbg.declare(metadata %struct.wfsptr* %wftemp, metadata !149, metadata !DIExpression()), !dbg !150
  %0 = load %struct.wfsptr*, %struct.wfsptr** %a_fptr.addr, align 8, !dbg !151
  %1 = bitcast %struct.wfsptr* %wftemp to i8*, !dbg !152
  %2 = bitcast %struct.wfsptr* %0 to i8*, !dbg !152
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %1, i8* align 8 %2, i64 8, i1 false), !dbg !152
  %3 = load %struct.wfsptr*, %struct.wfsptr** %a_fptr.addr, align 8, !dbg !153
  %4 = load %struct.wfsptr*, %struct.wfsptr** %b_fptr.addr, align 8, !dbg !154
  %5 = bitcast %struct.wfsptr* %3 to i8*, !dbg !155
  %6 = bitcast %struct.wfsptr* %4 to i8*, !dbg !155
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %5, i8* align 8 %6, i64 8, i1 false), !dbg !155
  %7 = load %struct.wfsptr*, %struct.wfsptr** %b_fptr.addr, align 8, !dbg !156
  %8 = bitcast %struct.wfsptr* %7 to i8*, !dbg !157
  %9 = bitcast %struct.wfsptr* %wftemp to i8*, !dbg !157
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %8, i8* align 8 %9, i64 8, i1 false), !dbg !157
  ret void, !dbg !158
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #2

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @moo(i8 signext %x, i32 %op1, i32 %op2) #0 !dbg !159 {
entry:
  %x.addr = alloca i8, align 1
  %op1.addr = alloca i32, align 4
  %op2.addr = alloca i32, align 4
  %a_fptr = alloca %struct.fptr, align 8
  %s_fptr = alloca %struct.fptr, align 8
  %m_fptr = alloca %struct.fsptr, align 8
  %n_fptr = alloca %struct.fsptr, align 8
  %w_fptr = alloca %struct.wfsptr, align 8
  %x_fptr = alloca %struct.wfsptr, align 8
  %k_fptr = alloca %struct.fsptr, align 8
  %y_fptr = alloca %struct.wfsptr, align 8
  %t_fptr = alloca %struct.fptr*, align 8
  store i8 %x, i8* %x.addr, align 1
  call void @llvm.dbg.declare(metadata i8* %x.addr, metadata !163, metadata !DIExpression()), !dbg !164
  store i32 %op1, i32* %op1.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %op1.addr, metadata !165, metadata !DIExpression()), !dbg !166
  store i32 %op2, i32* %op2.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %op2.addr, metadata !167, metadata !DIExpression()), !dbg !168
  call void @llvm.dbg.declare(metadata %struct.fptr* %a_fptr, metadata !169, metadata !DIExpression()), !dbg !170
  %p_fptr = getelementptr inbounds %struct.fptr, %struct.fptr* %a_fptr, i32 0, i32 0, !dbg !171
  store i32 (i32, i32)* @plus, i32 (i32, i32)** %p_fptr, align 8, !dbg !172
  call void @llvm.dbg.declare(metadata %struct.fptr* %s_fptr, metadata !173, metadata !DIExpression()), !dbg !174
  %p_fptr1 = getelementptr inbounds %struct.fptr, %struct.fptr* %s_fptr, i32 0, i32 0, !dbg !175
  store i32 (i32, i32)* @minus, i32 (i32, i32)** %p_fptr1, align 8, !dbg !176
  call void @llvm.dbg.declare(metadata %struct.fsptr* %m_fptr, metadata !177, metadata !DIExpression()), !dbg !178
  %sptr = getelementptr inbounds %struct.fsptr, %struct.fsptr* %m_fptr, i32 0, i32 0, !dbg !179
  store %struct.fptr* %a_fptr, %struct.fptr** %sptr, align 8, !dbg !180
  call void @llvm.dbg.declare(metadata %struct.fsptr* %n_fptr, metadata !181, metadata !DIExpression()), !dbg !182
  %sptr2 = getelementptr inbounds %struct.fsptr, %struct.fsptr* %n_fptr, i32 0, i32 0, !dbg !183
  store %struct.fptr* %s_fptr, %struct.fptr** %sptr2, align 8, !dbg !184
  call void @llvm.dbg.declare(metadata %struct.wfsptr* %w_fptr, metadata !185, metadata !DIExpression()), !dbg !186
  %wfptr = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %w_fptr, i32 0, i32 0, !dbg !187
  store %struct.fsptr* %m_fptr, %struct.fsptr** %wfptr, align 8, !dbg !188
  call void @llvm.dbg.declare(metadata %struct.wfsptr* %x_fptr, metadata !189, metadata !DIExpression()), !dbg !190
  call void @make_simple_alias(%struct.wfsptr* %x_fptr, %struct.fsptr* %n_fptr), !dbg !191
  call void @llvm.dbg.declare(metadata %struct.fsptr* %k_fptr, metadata !192, metadata !DIExpression()), !dbg !193
  call void @llvm.dbg.declare(metadata %struct.wfsptr* %y_fptr, metadata !194, metadata !DIExpression()), !dbg !195
  %wfptr3 = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %y_fptr, i32 0, i32 0, !dbg !196
  store %struct.fsptr* %k_fptr, %struct.fsptr** %wfptr3, align 8, !dbg !197
  call void @make_alias(%struct.wfsptr* %y_fptr, %struct.wfsptr* %x_fptr), !dbg !198
  %sptr4 = getelementptr inbounds %struct.fsptr, %struct.fsptr* %n_fptr, i32 0, i32 0, !dbg !199
  store %struct.fptr* %s_fptr, %struct.fptr** %sptr4, align 8, !dbg !200
  call void @llvm.dbg.declare(metadata %struct.fptr** %t_fptr, metadata !201, metadata !DIExpression()), !dbg !202
  store %struct.fptr* null, %struct.fptr** %t_fptr, align 8, !dbg !202
  %0 = load i32, i32* %op1.addr, align 4, !dbg !203
  %1 = load i32, i32* %op2.addr, align 4, !dbg !204
  %wfptr5 = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %y_fptr, i32 0, i32 0, !dbg !205
  %2 = load %struct.fsptr*, %struct.fsptr** %wfptr5, align 8, !dbg !205
  %call = call %struct.fptr* @clever(i32 %0, i32 %1, %struct.fsptr* %m_fptr, %struct.fsptr* %2), !dbg !206
  store %struct.fptr* %call, %struct.fptr** %t_fptr, align 8, !dbg !207
  %3 = load %struct.fptr*, %struct.fptr** %t_fptr, align 8, !dbg !208
  %p_fptr6 = getelementptr inbounds %struct.fptr, %struct.fptr* %3, i32 0, i32 0, !dbg !209
  %4 = load i32 (i32, i32)*, i32 (i32, i32)** %p_fptr6, align 8, !dbg !209
  %5 = load i32, i32* %op1.addr, align 4, !dbg !210
  %6 = load i32, i32* %op2.addr, align 4, !dbg !211
  %call7 = call i32 %4(i32 %5, i32 %6), !dbg !208
  %sptr8 = getelementptr inbounds %struct.fsptr, %struct.fsptr* %m_fptr, i32 0, i32 0, !dbg !212
  %7 = load %struct.fptr*, %struct.fptr** %sptr8, align 8, !dbg !212
  %p_fptr9 = getelementptr inbounds %struct.fptr, %struct.fptr* %7, i32 0, i32 0, !dbg !213
  %8 = load i32 (i32, i32)*, i32 (i32, i32)** %p_fptr9, align 8, !dbg !213
  %9 = load i32, i32* %op1.addr, align 4, !dbg !214
  %10 = load i32, i32* %op2.addr, align 4, !dbg !215
  %call10 = call i32 %8(i32 %9, i32 %10), !dbg !216
  call void @swap_w(%struct.wfsptr* %x_fptr, %struct.wfsptr* %w_fptr), !dbg !217
  %wfptr11 = getelementptr inbounds %struct.wfsptr, %struct.wfsptr* %w_fptr, i32 0, i32 0, !dbg !218
  %11 = load %struct.fsptr*, %struct.fsptr** %wfptr11, align 8, !dbg !218
  %sptr12 = getelementptr inbounds %struct.fsptr, %struct.fsptr* %11, i32 0, i32 0, !dbg !219
  %12 = load %struct.fptr*, %struct.fptr** %sptr12, align 8, !dbg !219
  %p_fptr13 = getelementptr inbounds %struct.fptr, %struct.fptr* %12, i32 0, i32 0, !dbg !220
  %13 = load i32 (i32, i32)*, i32 (i32, i32)** %p_fptr13, align 8, !dbg !220
  %14 = load i32, i32* %op1.addr, align 4, !dbg !221
  %15 = load i32, i32* %op2.addr, align 4, !dbg !222
  %call14 = call i32 %13(i32 %14, i32 %15), !dbg !223
  ret i32 0, !dbg !224
}

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable willreturn }
attributes #2 = { argmemonly nounwind willreturn }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5}
!llvm.ident = !{!6}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 10.0.0 ", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "../test33.c", directory: "/root/PointerAnalyse/test/testll")
!2 = !{}
!3 = !{i32 7, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{!"clang version 10.0.0 "}
!7 = distinct !DISubprogram(name: "plus", scope: !1, file: !1, line: 14, type: !8, scopeLine: 14, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!8 = !DISubroutineType(types: !9)
!9 = !{!10, !10, !10}
!10 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!11 = !DILocalVariable(name: "a", arg: 1, scope: !7, file: !1, line: 14, type: !10)
!12 = !DILocation(line: 14, column: 14, scope: !7)
!13 = !DILocalVariable(name: "b", arg: 2, scope: !7, file: !1, line: 14, type: !10)
!14 = !DILocation(line: 14, column: 21, scope: !7)
!15 = !DILocation(line: 15, column: 11, scope: !7)
!16 = !DILocation(line: 15, column: 13, scope: !7)
!17 = !DILocation(line: 15, column: 12, scope: !7)
!18 = !DILocation(line: 15, column: 4, scope: !7)
!19 = distinct !DISubprogram(name: "minus", scope: !1, file: !1, line: 18, type: !8, scopeLine: 18, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!20 = !DILocalVariable(name: "a", arg: 1, scope: !19, file: !1, line: 18, type: !10)
!21 = !DILocation(line: 18, column: 15, scope: !19)
!22 = !DILocalVariable(name: "b", arg: 2, scope: !19, file: !1, line: 18, type: !10)
!23 = !DILocation(line: 18, column: 22, scope: !19)
!24 = !DILocation(line: 19, column: 11, scope: !19)
!25 = !DILocation(line: 19, column: 13, scope: !19)
!26 = !DILocation(line: 19, column: 12, scope: !19)
!27 = !DILocation(line: 19, column: 4, scope: !19)
!28 = distinct !DISubprogram(name: "foo", scope: !1, file: !1, line: 21, type: !29, scopeLine: 21, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!29 = !DISubroutineType(types: !30)
!30 = !{!31, !10, !10, !36, !36}
!31 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !32, size: 64)
!32 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "fptr", file: !1, line: 2, size: 64, elements: !33)
!33 = !{!34}
!34 = !DIDerivedType(tag: DW_TAG_member, name: "p_fptr", scope: !32, file: !1, line: 4, baseType: !35, size: 64)
!35 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !8, size: 64)
!36 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !37, size: 64)
!37 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "wfsptr", file: !1, line: 10, size: 64, elements: !38)
!38 = !{!39}
!39 = !DIDerivedType(tag: DW_TAG_member, name: "wfptr", scope: !37, file: !1, line: 12, baseType: !40, size: 64)
!40 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !41, size: 64)
!41 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "fsptr", file: !1, line: 6, size: 64, elements: !42)
!42 = !{!43}
!43 = !DIDerivedType(tag: DW_TAG_member, name: "sptr", scope: !41, file: !1, line: 8, baseType: !31, size: 64)
!44 = !DILocalVariable(name: "a", arg: 1, scope: !28, file: !1, line: 21, type: !10)
!45 = !DILocation(line: 21, column: 23, scope: !28)
!46 = !DILocalVariable(name: "b", arg: 2, scope: !28, file: !1, line: 21, type: !10)
!47 = !DILocation(line: 21, column: 30, scope: !28)
!48 = !DILocalVariable(name: "a_fptr", arg: 3, scope: !28, file: !1, line: 21, type: !36)
!49 = !DILocation(line: 21, column: 49, scope: !28)
!50 = !DILocalVariable(name: "b_fptr", arg: 4, scope: !28, file: !1, line: 21, type: !36)
!51 = !DILocation(line: 21, column: 73, scope: !28)
!52 = !DILocation(line: 22, column: 7, scope: !53)
!53 = distinct !DILexicalBlock(scope: !28, file: !1, line: 22, column: 7)
!54 = !DILocation(line: 22, column: 8, scope: !53)
!55 = !DILocation(line: 22, column: 11, scope: !53)
!56 = !DILocation(line: 22, column: 14, scope: !53)
!57 = !DILocation(line: 22, column: 15, scope: !53)
!58 = !DILocation(line: 22, column: 7, scope: !28)
!59 = !DILocalVariable(name: "temp", scope: !60, file: !1, line: 24, type: !40)
!60 = distinct !DILexicalBlock(scope: !53, file: !1, line: 23, column: 4)
!61 = !DILocation(line: 24, column: 20, scope: !60)
!62 = !DILocation(line: 24, column: 25, scope: !60)
!63 = !DILocation(line: 24, column: 33, scope: !60)
!64 = !DILocation(line: 25, column: 27, scope: !60)
!65 = !DILocation(line: 25, column: 35, scope: !60)
!66 = !DILocation(line: 25, column: 42, scope: !60)
!67 = !DILocation(line: 25, column: 5, scope: !60)
!68 = !DILocation(line: 25, column: 13, scope: !60)
!69 = !DILocation(line: 25, column: 20, scope: !60)
!70 = !DILocation(line: 25, column: 25, scope: !60)
!71 = !DILocation(line: 26, column: 26, scope: !60)
!72 = !DILocation(line: 26, column: 32, scope: !60)
!73 = !DILocation(line: 26, column: 5, scope: !60)
!74 = !DILocation(line: 26, column: 13, scope: !60)
!75 = !DILocation(line: 26, column: 20, scope: !60)
!76 = !DILocation(line: 26, column: 25, scope: !60)
!77 = !DILocation(line: 27, column: 5, scope: !60)
!78 = !DILocation(line: 27, column: 13, scope: !60)
!79 = !DILocation(line: 27, column: 20, scope: !60)
!80 = !DILocation(line: 27, column: 26, scope: !60)
!81 = !DILocation(line: 27, column: 33, scope: !60)
!82 = !DILocation(line: 27, column: 35, scope: !60)
!83 = !DILocation(line: 28, column: 12, scope: !60)
!84 = !DILocation(line: 28, column: 20, scope: !60)
!85 = !DILocation(line: 28, column: 27, scope: !60)
!86 = !DILocation(line: 28, column: 5, scope: !60)
!87 = !DILocation(line: 30, column: 11, scope: !28)
!88 = !DILocation(line: 30, column: 19, scope: !28)
!89 = !DILocation(line: 30, column: 26, scope: !28)
!90 = !DILocation(line: 30, column: 4, scope: !28)
!91 = !DILocation(line: 31, column: 1, scope: !28)
!92 = distinct !DISubprogram(name: "clever", scope: !1, file: !1, line: 33, type: !93, scopeLine: 33, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!93 = !DISubroutineType(types: !94)
!94 = !{!31, !10, !10, !40, !40}
!95 = !DILocalVariable(name: "a", arg: 1, scope: !92, file: !1, line: 33, type: !10)
!96 = !DILocation(line: 33, column: 26, scope: !92)
!97 = !DILocalVariable(name: "b", arg: 2, scope: !92, file: !1, line: 33, type: !10)
!98 = !DILocation(line: 33, column: 33, scope: !92)
!99 = !DILocalVariable(name: "a_fptr", arg: 3, scope: !92, file: !1, line: 33, type: !40)
!100 = !DILocation(line: 33, column: 51, scope: !92)
!101 = !DILocalVariable(name: "b_fptr", arg: 4, scope: !92, file: !1, line: 33, type: !40)
!102 = !DILocation(line: 33, column: 74, scope: !92)
!103 = !DILocalVariable(name: "t1_fptr", scope: !92, file: !1, line: 34, type: !37)
!104 = !DILocation(line: 34, column: 18, scope: !92)
!105 = !DILocation(line: 35, column: 18, scope: !92)
!106 = !DILocation(line: 35, column: 12, scope: !92)
!107 = !DILocation(line: 35, column: 17, scope: !92)
!108 = !DILocalVariable(name: "t2_fptr", scope: !92, file: !1, line: 36, type: !37)
!109 = !DILocation(line: 36, column: 18, scope: !92)
!110 = !DILocation(line: 37, column: 18, scope: !92)
!111 = !DILocation(line: 37, column: 12, scope: !92)
!112 = !DILocation(line: 37, column: 17, scope: !92)
!113 = !DILocation(line: 38, column: 15, scope: !92)
!114 = !DILocation(line: 38, column: 17, scope: !92)
!115 = !DILocation(line: 38, column: 11, scope: !92)
!116 = !DILocation(line: 38, column: 4, scope: !92)
!117 = distinct !DISubprogram(name: "make_simple_alias", scope: !1, file: !1, line: 41, type: !118, scopeLine: 42, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!118 = !DISubroutineType(types: !119)
!119 = !{null, !36, !40}
!120 = !DILocalVariable(name: "a_fptr", arg: 1, scope: !117, file: !1, line: 41, type: !36)
!121 = !DILocation(line: 41, column: 40, scope: !117)
!122 = !DILocalVariable(name: "b_fptr", arg: 2, scope: !117, file: !1, line: 41, type: !40)
!123 = !DILocation(line: 41, column: 62, scope: !117)
!124 = !DILocation(line: 43, column: 17, scope: !117)
!125 = !DILocation(line: 43, column: 3, scope: !117)
!126 = !DILocation(line: 43, column: 11, scope: !117)
!127 = !DILocation(line: 43, column: 16, scope: !117)
!128 = !DILocation(line: 44, column: 1, scope: !117)
!129 = distinct !DISubprogram(name: "make_alias", scope: !1, file: !1, line: 45, type: !130, scopeLine: 46, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!130 = !DISubroutineType(types: !131)
!131 = !{null, !36, !36}
!132 = !DILocalVariable(name: "a_fptr", arg: 1, scope: !129, file: !1, line: 45, type: !36)
!133 = !DILocation(line: 45, column: 32, scope: !129)
!134 = !DILocalVariable(name: "b_fptr", arg: 2, scope: !129, file: !1, line: 45, type: !36)
!135 = !DILocation(line: 45, column: 55, scope: !129)
!136 = !DILocation(line: 47, column: 23, scope: !129)
!137 = !DILocation(line: 47, column: 31, scope: !129)
!138 = !DILocation(line: 47, column: 38, scope: !129)
!139 = !DILocation(line: 47, column: 3, scope: !129)
!140 = !DILocation(line: 47, column: 11, scope: !129)
!141 = !DILocation(line: 47, column: 18, scope: !129)
!142 = !DILocation(line: 47, column: 22, scope: !129)
!143 = !DILocation(line: 48, column: 1, scope: !129)
!144 = distinct !DISubprogram(name: "swap_w", scope: !1, file: !1, line: 49, type: !130, scopeLine: 50, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!145 = !DILocalVariable(name: "a_fptr", arg: 1, scope: !144, file: !1, line: 49, type: !36)
!146 = !DILocation(line: 49, column: 29, scope: !144)
!147 = !DILocalVariable(name: "b_fptr", arg: 2, scope: !144, file: !1, line: 49, type: !36)
!148 = !DILocation(line: 49, column: 52, scope: !144)
!149 = !DILocalVariable(name: "wftemp", scope: !144, file: !1, line: 51, type: !37)
!150 = !DILocation(line: 51, column: 20, scope: !144)
!151 = !DILocation(line: 51, column: 28, scope: !144)
!152 = !DILocation(line: 51, column: 27, scope: !144)
!153 = !DILocation(line: 52, column: 7, scope: !144)
!154 = !DILocation(line: 52, column: 15, scope: !144)
!155 = !DILocation(line: 52, column: 14, scope: !144)
!156 = !DILocation(line: 53, column: 7, scope: !144)
!157 = !DILocation(line: 53, column: 14, scope: !144)
!158 = !DILocation(line: 54, column: 1, scope: !144)
!159 = distinct !DISubprogram(name: "moo", scope: !1, file: !1, line: 55, type: !160, scopeLine: 55, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!160 = !DISubroutineType(types: !161)
!161 = !{!10, !162, !10, !10}
!162 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!163 = !DILocalVariable(name: "x", arg: 1, scope: !159, file: !1, line: 55, type: !162)
!164 = !DILocation(line: 55, column: 14, scope: !159)
!165 = !DILocalVariable(name: "op1", arg: 2, scope: !159, file: !1, line: 55, type: !10)
!166 = !DILocation(line: 55, column: 21, scope: !159)
!167 = !DILocalVariable(name: "op2", arg: 3, scope: !159, file: !1, line: 55, type: !10)
!168 = !DILocation(line: 55, column: 30, scope: !159)
!169 = !DILocalVariable(name: "a_fptr", scope: !159, file: !1, line: 56, type: !32)
!170 = !DILocation(line: 56, column: 17, scope: !159)
!171 = !DILocation(line: 57, column: 12, scope: !159)
!172 = !DILocation(line: 57, column: 18, scope: !159)
!173 = !DILocalVariable(name: "s_fptr", scope: !159, file: !1, line: 58, type: !32)
!174 = !DILocation(line: 58, column: 17, scope: !159)
!175 = !DILocation(line: 59, column: 12, scope: !159)
!176 = !DILocation(line: 59, column: 18, scope: !159)
!177 = !DILocalVariable(name: "m_fptr", scope: !159, file: !1, line: 61, type: !41)
!178 = !DILocation(line: 61, column: 18, scope: !159)
!179 = !DILocation(line: 62, column: 12, scope: !159)
!180 = !DILocation(line: 62, column: 16, scope: !159)
!181 = !DILocalVariable(name: "n_fptr", scope: !159, file: !1, line: 63, type: !41)
!182 = !DILocation(line: 63, column: 18, scope: !159)
!183 = !DILocation(line: 64, column: 12, scope: !159)
!184 = !DILocation(line: 64, column: 16, scope: !159)
!185 = !DILocalVariable(name: "w_fptr", scope: !159, file: !1, line: 66, type: !37)
!186 = !DILocation(line: 66, column: 19, scope: !159)
!187 = !DILocation(line: 67, column: 12, scope: !159)
!188 = !DILocation(line: 67, column: 17, scope: !159)
!189 = !DILocalVariable(name: "x_fptr", scope: !159, file: !1, line: 69, type: !37)
!190 = !DILocation(line: 69, column: 19, scope: !159)
!191 = !DILocation(line: 70, column: 5, scope: !159)
!192 = !DILocalVariable(name: "k_fptr", scope: !159, file: !1, line: 72, type: !41)
!193 = !DILocation(line: 72, column: 18, scope: !159)
!194 = !DILocalVariable(name: "y_fptr", scope: !159, file: !1, line: 73, type: !37)
!195 = !DILocation(line: 73, column: 19, scope: !159)
!196 = !DILocation(line: 74, column: 12, scope: !159)
!197 = !DILocation(line: 74, column: 17, scope: !159)
!198 = !DILocation(line: 75, column: 5, scope: !159)
!199 = !DILocation(line: 77, column: 12, scope: !159)
!200 = !DILocation(line: 77, column: 16, scope: !159)
!201 = !DILocalVariable(name: "t_fptr", scope: !159, file: !1, line: 79, type: !31)
!202 = !DILocation(line: 79, column: 18, scope: !159)
!203 = !DILocation(line: 81, column: 21, scope: !159)
!204 = !DILocation(line: 81, column: 26, scope: !159)
!205 = !DILocation(line: 81, column: 47, scope: !159)
!206 = !DILocation(line: 81, column: 14, scope: !159)
!207 = !DILocation(line: 81, column: 12, scope: !159)
!208 = !DILocation(line: 82, column: 5, scope: !159)
!209 = !DILocation(line: 82, column: 13, scope: !159)
!210 = !DILocation(line: 82, column: 20, scope: !159)
!211 = !DILocation(line: 82, column: 25, scope: !159)
!212 = !DILocation(line: 83, column: 12, scope: !159)
!213 = !DILocation(line: 83, column: 18, scope: !159)
!214 = !DILocation(line: 83, column: 25, scope: !159)
!215 = !DILocation(line: 83, column: 29, scope: !159)
!216 = !DILocation(line: 83, column: 5, scope: !159)
!217 = !DILocation(line: 84, column: 5, scope: !159)
!218 = !DILocation(line: 85, column: 12, scope: !159)
!219 = !DILocation(line: 85, column: 19, scope: !159)
!220 = !DILocation(line: 85, column: 25, scope: !159)
!221 = !DILocation(line: 85, column: 32, scope: !159)
!222 = !DILocation(line: 85, column: 36, scope: !159)
!223 = !DILocation(line: 85, column: 5, scope: !159)
!224 = !DILocation(line: 87, column: 5, scope: !159)
