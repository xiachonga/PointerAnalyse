; ModuleID = '../test13.c'
source_filename = "../test13.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.fptr = type { i32 (i32, i32)* }

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
define dso_local i32 @clever(i32 %a, i32 %b, i32 (i32, i32)* %a_fptr.coerce) #0 !dbg !28 {
entry:
  %a_fptr = alloca %struct.fptr, align 8
  %a.addr = alloca i32, align 4
  %b.addr = alloca i32, align 4
  %coerce.dive = getelementptr inbounds %struct.fptr, %struct.fptr* %a_fptr, i32 0, i32 0
  store i32 (i32, i32)* %a_fptr.coerce, i32 (i32, i32)** %coerce.dive, align 8
  store i32 %a, i32* %a.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %a.addr, metadata !35, metadata !DIExpression()), !dbg !36
  store i32 %b, i32* %b.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %b.addr, metadata !37, metadata !DIExpression()), !dbg !38
  call void @llvm.dbg.declare(metadata %struct.fptr* %a_fptr, metadata !39, metadata !DIExpression()), !dbg !40
  %p_fptr = getelementptr inbounds %struct.fptr, %struct.fptr* %a_fptr, i32 0, i32 0, !dbg !41
  %0 = load i32 (i32, i32)*, i32 (i32, i32)** %p_fptr, align 8, !dbg !41
  %1 = load i32, i32* %a.addr, align 4, !dbg !42
  %2 = load i32, i32* %b.addr, align 4, !dbg !43
  %call = call i32 %0(i32 %1, i32 %2), !dbg !44
  ret i32 %call, !dbg !45
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @moo(i8 signext %x, i32 %op1, i32 %op2) #0 !dbg !46 {
entry:
  %x.addr = alloca i8, align 1
  %op1.addr = alloca i32, align 4
  %op2.addr = alloca i32, align 4
  %a_fptr = alloca i32 (i32, i32)*, align 8
  %s_fptr = alloca i32 (i32, i32)*, align 8
  %t_fptr = alloca %struct.fptr, align 8
  %result = alloca i32, align 4
  store i8 %x, i8* %x.addr, align 1
  call void @llvm.dbg.declare(metadata i8* %x.addr, metadata !50, metadata !DIExpression()), !dbg !51
  store i32 %op1, i32* %op1.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %op1.addr, metadata !52, metadata !DIExpression()), !dbg !53
  store i32 %op2, i32* %op2.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %op2.addr, metadata !54, metadata !DIExpression()), !dbg !55
  call void @llvm.dbg.declare(metadata i32 (i32, i32)** %a_fptr, metadata !56, metadata !DIExpression()), !dbg !57
  store i32 (i32, i32)* @plus, i32 (i32, i32)** %a_fptr, align 8, !dbg !57
  call void @llvm.dbg.declare(metadata i32 (i32, i32)** %s_fptr, metadata !58, metadata !DIExpression()), !dbg !59
  store i32 (i32, i32)* @minus, i32 (i32, i32)** %s_fptr, align 8, !dbg !59
  call void @llvm.dbg.declare(metadata %struct.fptr* %t_fptr, metadata !60, metadata !DIExpression()), !dbg !61
  %0 = bitcast %struct.fptr* %t_fptr to i8*, !dbg !61
  call void @llvm.memset.p0i8.i64(i8* align 8 %0, i8 0, i64 8, i1 false), !dbg !61
  %1 = load i8, i8* %x.addr, align 1, !dbg !62
  %conv = sext i8 %1 to i32, !dbg !62
  %cmp = icmp eq i32 %conv, 43, !dbg !64
  br i1 %cmp, label %if.then, label %if.else, !dbg !65

if.then:                                          ; preds = %entry
  %2 = load i32 (i32, i32)*, i32 (i32, i32)** %a_fptr, align 8, !dbg !66
  %p_fptr = getelementptr inbounds %struct.fptr, %struct.fptr* %t_fptr, i32 0, i32 0, !dbg !68
  store i32 (i32, i32)* %2, i32 (i32, i32)** %p_fptr, align 8, !dbg !69
  br label %if.end7, !dbg !70

if.else:                                          ; preds = %entry
  %3 = load i8, i8* %x.addr, align 1, !dbg !71
  %conv2 = sext i8 %3 to i32, !dbg !71
  %cmp3 = icmp eq i32 %conv2, 45, !dbg !73
  br i1 %cmp3, label %if.then5, label %if.end, !dbg !74

if.then5:                                         ; preds = %if.else
  %4 = load i32 (i32, i32)*, i32 (i32, i32)** %s_fptr, align 8, !dbg !75
  %p_fptr6 = getelementptr inbounds %struct.fptr, %struct.fptr* %t_fptr, i32 0, i32 0, !dbg !77
  store i32 (i32, i32)* %4, i32 (i32, i32)** %p_fptr6, align 8, !dbg !78
  br label %if.end, !dbg !79

if.end:                                           ; preds = %if.then5, %if.else
  br label %if.end7

if.end7:                                          ; preds = %if.end, %if.then
  call void @llvm.dbg.declare(metadata i32* %result, metadata !80, metadata !DIExpression()), !dbg !82
  %5 = load i32, i32* %op1.addr, align 4, !dbg !83
  %6 = load i32, i32* %op2.addr, align 4, !dbg !84
  %coerce.dive = getelementptr inbounds %struct.fptr, %struct.fptr* %t_fptr, i32 0, i32 0, !dbg !85
  %7 = load i32 (i32, i32)*, i32 (i32, i32)** %coerce.dive, align 8, !dbg !85
  %call = call i32 @clever(i32 %5, i32 %6, i32 (i32, i32)* %7), !dbg !85
  store i32 %call, i32* %result, align 4, !dbg !82
  ret i32 0, !dbg !86
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i1 immarg) #2

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable willreturn }
attributes #2 = { argmemonly nounwind willreturn }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5}
!llvm.ident = !{!6}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 10.0.0 ", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "../test13.c", directory: "/root/PointerAnalyse/test/testll")
!2 = !{}
!3 = !{i32 7, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{!"clang version 10.0.0 "}
!7 = distinct !DISubprogram(name: "plus", scope: !1, file: !1, line: 6, type: !8, scopeLine: 6, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!8 = !DISubroutineType(types: !9)
!9 = !{!10, !10, !10}
!10 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!11 = !DILocalVariable(name: "a", arg: 1, scope: !7, file: !1, line: 6, type: !10)
!12 = !DILocation(line: 6, column: 14, scope: !7)
!13 = !DILocalVariable(name: "b", arg: 2, scope: !7, file: !1, line: 6, type: !10)
!14 = !DILocation(line: 6, column: 21, scope: !7)
!15 = !DILocation(line: 7, column: 11, scope: !7)
!16 = !DILocation(line: 7, column: 13, scope: !7)
!17 = !DILocation(line: 7, column: 12, scope: !7)
!18 = !DILocation(line: 7, column: 4, scope: !7)
!19 = distinct !DISubprogram(name: "minus", scope: !1, file: !1, line: 10, type: !8, scopeLine: 10, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!20 = !DILocalVariable(name: "a", arg: 1, scope: !19, file: !1, line: 10, type: !10)
!21 = !DILocation(line: 10, column: 15, scope: !19)
!22 = !DILocalVariable(name: "b", arg: 2, scope: !19, file: !1, line: 10, type: !10)
!23 = !DILocation(line: 10, column: 22, scope: !19)
!24 = !DILocation(line: 11, column: 11, scope: !19)
!25 = !DILocation(line: 11, column: 13, scope: !19)
!26 = !DILocation(line: 11, column: 12, scope: !19)
!27 = !DILocation(line: 11, column: 4, scope: !19)
!28 = distinct !DISubprogram(name: "clever", scope: !1, file: !1, line: 14, type: !29, scopeLine: 14, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!29 = !DISubroutineType(types: !30)
!30 = !{!10, !10, !10, !31}
!31 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "fptr", file: !1, line: 2, size: 64, elements: !32)
!32 = !{!33}
!33 = !DIDerivedType(tag: DW_TAG_member, name: "p_fptr", scope: !31, file: !1, line: 4, baseType: !34, size: 64)
!34 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !8, size: 64)
!35 = !DILocalVariable(name: "a", arg: 1, scope: !28, file: !1, line: 14, type: !10)
!36 = !DILocation(line: 14, column: 16, scope: !28)
!37 = !DILocalVariable(name: "b", arg: 2, scope: !28, file: !1, line: 14, type: !10)
!38 = !DILocation(line: 14, column: 23, scope: !28)
!39 = !DILocalVariable(name: "a_fptr", arg: 3, scope: !28, file: !1, line: 14, type: !31)
!40 = !DILocation(line: 14, column: 38, scope: !28)
!41 = !DILocation(line: 15, column: 19, scope: !28)
!42 = !DILocation(line: 15, column: 26, scope: !28)
!43 = !DILocation(line: 15, column: 29, scope: !28)
!44 = !DILocation(line: 15, column: 12, scope: !28)
!45 = !DILocation(line: 15, column: 5, scope: !28)
!46 = distinct !DISubprogram(name: "moo", scope: !1, file: !1, line: 19, type: !47, scopeLine: 19, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!47 = !DISubroutineType(types: !48)
!48 = !{!10, !49, !10, !10}
!49 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!50 = !DILocalVariable(name: "x", arg: 1, scope: !46, file: !1, line: 19, type: !49)
!51 = !DILocation(line: 19, column: 14, scope: !46)
!52 = !DILocalVariable(name: "op1", arg: 2, scope: !46, file: !1, line: 19, type: !10)
!53 = !DILocation(line: 19, column: 21, scope: !46)
!54 = !DILocalVariable(name: "op2", arg: 3, scope: !46, file: !1, line: 19, type: !10)
!55 = !DILocation(line: 19, column: 30, scope: !46)
!56 = !DILocalVariable(name: "a_fptr", scope: !46, file: !1, line: 20, type: !34)
!57 = !DILocation(line: 20, column: 11, scope: !46)
!58 = !DILocalVariable(name: "s_fptr", scope: !46, file: !1, line: 21, type: !34)
!59 = !DILocation(line: 21, column: 11, scope: !46)
!60 = !DILocalVariable(name: "t_fptr", scope: !46, file: !1, line: 22, type: !31)
!61 = !DILocation(line: 22, column: 17, scope: !46)
!62 = !DILocation(line: 24, column: 9, scope: !63)
!63 = distinct !DILexicalBlock(scope: !46, file: !1, line: 24, column: 9)
!64 = !DILocation(line: 24, column: 11, scope: !63)
!65 = !DILocation(line: 24, column: 9, scope: !46)
!66 = !DILocation(line: 25, column: 24, scope: !67)
!67 = distinct !DILexicalBlock(scope: !63, file: !1, line: 24, column: 19)
!68 = !DILocation(line: 25, column: 15, scope: !67)
!69 = !DILocation(line: 25, column: 22, scope: !67)
!70 = !DILocation(line: 26, column: 5, scope: !67)
!71 = !DILocation(line: 27, column: 14, scope: !72)
!72 = distinct !DILexicalBlock(scope: !63, file: !1, line: 27, column: 14)
!73 = !DILocation(line: 27, column: 16, scope: !72)
!74 = !DILocation(line: 27, column: 14, scope: !63)
!75 = !DILocation(line: 28, column: 24, scope: !76)
!76 = distinct !DILexicalBlock(scope: !72, file: !1, line: 27, column: 24)
!77 = !DILocation(line: 28, column: 16, scope: !76)
!78 = !DILocation(line: 28, column: 22, scope: !76)
!79 = !DILocation(line: 29, column: 5, scope: !76)
!80 = !DILocalVariable(name: "result", scope: !46, file: !1, line: 31, type: !81)
!81 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!82 = !DILocation(line: 31, column: 14, scope: !46)
!83 = !DILocation(line: 31, column: 30, scope: !46)
!84 = !DILocation(line: 31, column: 35, scope: !46)
!85 = !DILocation(line: 31, column: 23, scope: !46)
!86 = !DILocation(line: 32, column: 5, scope: !46)
