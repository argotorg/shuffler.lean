; ModuleID = '/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo/spikes/clight-permute/build/equiv-alive2/rejected-depth-extended/n18/linked.bc'
source_filename = "llvm-link"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.TypeMismatchData = type <{ { ptr, i32, i32 }, ptr, i8, i8, [6 x i8] }>
%struct.OverflowData = type { { ptr, i32, i32 }, ptr }
%"class.__ubsan::TypeDescriptor" = type <{ i16, i16, [1 x i8], i8 }>
%struct.ImplicitConversionData = type <{ { ptr, i32, i32 }, ptr, ptr, i8, [7 x i8] }>

$_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv = comdat any

$_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv = comdat any

$_ZNK7__ubsan14TypeDescriptor7getKindEv = comdat any

@.str = private unnamed_addr constant [14 x i8] c"reject_inputs\00", align 1, !dbg !0
@.src = private unnamed_addr constant [119 x i8] c"/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo/spikes/clight-permute/tests/equiv-alive2/rejected-driver.c\00", align 1
@0 = private unnamed_addr constant { i16, i16, [19 x i8] } { i16 -1, i16 0, [19 x i8] c"'unsigned int[39]'\00" }
@1 = private unnamed_addr constant { i16, i16, [15 x i8] } { i16 0, i16 10, [15 x i8] c"'unsigned int'\00" }
@2 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 25, i32 18 }, ptr @0, ptr @1 }
@3 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 27, i32 22 }, ptr @0, ptr @1 }
@4 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 27, i32 34 }, ptr @0, ptr @1 }
@5 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 28, i32 26 }, ptr @0, ptr @1 }
@6 = private unnamed_addr constant { i16, i16, [19 x i8] } { i16 -1, i16 0, [19 x i8] c"'unsigned int[18]'\00" }
@7 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 28, i32 9 }, ptr @6, ptr @1 }
@8 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 29, i32 19 }, ptr @0, ptr @1 }
@9 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 29, i32 9 }, ptr @6, ptr @1 }
@10 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 35, i32 18 }, ptr @0, ptr @1 }
@11 = private unnamed_addr constant { i16, i16, [18 x i8] } { i16 -1, i16 0, [18 x i8] c"'unsigned int[3]'\00" }
@12 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 35, i32 9 }, ptr @11, ptr @1 }
@.str.1 = private unnamed_addr constant [13 x i8] c"status == 2U\00", align 1, !dbg !7
@__PRETTY_FUNCTION__.checked_main = private unnamed_addr constant [23 x i8] c"int checked_main(void)\00", align 1, !dbg !12
@13 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 39, i32 9 }, ptr @6, ptr @1 }
@14 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 39, i32 9 }, ptr @0, ptr @1 }
@.str.2 = private unnamed_addr constant [27 x i8] c"permutation[i] == input[i]\00", align 1, !dbg !18
@15 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 40, i32 9 }, ptr @6, ptr @1 }
@16 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 40, i32 9 }, ptr @0, ptr @1 }
@.str.3 = private unnamed_addr constant [31 x i8] c"data[i] == input[REJECT_N + i]\00", align 1, !dbg !23
@17 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 44, i32 9 }, ptr @11, ptr @1 }
@.str.4 = private unnamed_addr constant [13 x i8] c"out[i] == 0U\00", align 1, !dbg !28
@.str.5 = private unnamed_addr constant [17 x i8] c"checks_completed\00", align 1, !dbg !30
@.str.49 = private unnamed_addr constant [2 x i8] c"+\00", align 1, !dbg !36
@.str.1.50 = private unnamed_addr constant [2 x i8] c"-\00", align 1, !dbg !42
@.str.2.51 = private unnamed_addr constant [2 x i8] c"*\00", align 1, !dbg !44
@.str.3.1 = private unnamed_addr constant [57 x i8] c"/build/source/runtime/Sanitizer/ubsan/ubsan_handlers.cpp\00", align 1, !dbg !46
@.str.4.2 = private unnamed_addr constant [19 x i8] c"undefined-behavior\00", align 1, !dbg !51
@.str.5.3 = private unnamed_addr constant [17 x i8] c"null-pointer-use\00", align 1, !dbg !57
@.str.6 = private unnamed_addr constant [20 x i8] c"nullptr-with-offset\00", align 1, !dbg !60
@.str.7 = private unnamed_addr constant [28 x i8] c"nullptr-with-nonzero-offset\00", align 1, !dbg !65
@.str.8 = private unnamed_addr constant [29 x i8] c"nullptr-after-nonzero-offset\00", align 1, !dbg !70
@.str.9 = private unnamed_addr constant [17 x i8] c"pointer-overflow\00", align 1, !dbg !75
@.str.10 = private unnamed_addr constant [23 x i8] c"misaligned-pointer-use\00", align 1, !dbg !77
@.str.11 = private unnamed_addr constant [21 x i8] c"alignment-assumption\00", align 1, !dbg !79
@.str.12 = private unnamed_addr constant [25 x i8] c"insufficient-object-size\00", align 1, !dbg !84
@.str.13 = private unnamed_addr constant [24 x i8] c"signed-integer-overflow\00", align 1, !dbg !89
@.str.14 = private unnamed_addr constant [26 x i8] c"unsigned-integer-overflow\00", align 1, !dbg !94
@.str.15 = private unnamed_addr constant [23 x i8] c"integer-divide-by-zero\00", align 1, !dbg !99
@.str.16 = private unnamed_addr constant [21 x i8] c"float-divide-by-zero\00", align 1, !dbg !101
@.str.17 = private unnamed_addr constant [20 x i8] c"invalid-builtin-use\00", align 1, !dbg !103
@.str.18 = private unnamed_addr constant [18 x i8] c"invalid-objc-cast\00", align 1, !dbg !105
@.str.19 = private unnamed_addr constant [37 x i8] c"implicit-unsigned-integer-truncation\00", align 1, !dbg !110
@.str.20 = private unnamed_addr constant [35 x i8] c"implicit-signed-integer-truncation\00", align 1, !dbg !115
@.str.21 = private unnamed_addr constant [29 x i8] c"implicit-integer-sign-change\00", align 1, !dbg !120
@.str.22 = private unnamed_addr constant [50 x i8] c"implicit-signed-integer-truncation-or-sign-change\00", align 1, !dbg !122
@.str.23 = private unnamed_addr constant [19 x i8] c"invalid-shift-base\00", align 1, !dbg !127
@.str.24 = private unnamed_addr constant [23 x i8] c"invalid-shift-exponent\00", align 1, !dbg !129
@.str.25 = private unnamed_addr constant [20 x i8] c"out-of-bounds-index\00", align 1, !dbg !131
@.str.26 = private unnamed_addr constant [17 x i8] c"unreachable-call\00", align 1, !dbg !133
@.str.27 = private unnamed_addr constant [15 x i8] c"missing-return\00", align 1, !dbg !135
@.str.28 = private unnamed_addr constant [23 x i8] c"non-positive-vla-index\00", align 1, !dbg !140
@.str.29 = private unnamed_addr constant [20 x i8] c"float-cast-overflow\00", align 1, !dbg !142
@.str.30 = private unnamed_addr constant [18 x i8] c"invalid-bool-load\00", align 1, !dbg !144
@.str.31 = private unnamed_addr constant [18 x i8] c"invalid-enum-load\00", align 1, !dbg !146
@.str.32 = private unnamed_addr constant [23 x i8] c"function-type-mismatch\00", align 1, !dbg !148
@.str.33 = private unnamed_addr constant [20 x i8] c"invalid-null-return\00", align 1, !dbg !150
@.str.34 = private unnamed_addr constant [22 x i8] c"invalid-null-argument\00", align 1, !dbg !152
@.str.35 = private unnamed_addr constant [22 x i8] c"dynamic-type-mismatch\00", align 1, !dbg !157
@.str.36 = private unnamed_addr constant [13 x i8] c"cfi-bad-type\00", align 1, !dbg !159
@.str.37 = private unnamed_addr constant [9 x i8] c"exec.err\00", align 1, !dbg !162
@.str.38 = private unnamed_addr constant [8 x i8] c"ptr.err\00", align 1, !dbg !167
@.str.39 = private unnamed_addr constant [13 x i8] c"overflow.err\00", align 1, !dbg !172
@.str.40 = private unnamed_addr constant [8 x i8] c"div.err\00", align 1, !dbg !174
@.str.41 = private unnamed_addr constant [24 x i8] c"invalid_builtin_use.err\00", align 1, !dbg !176
@.str.42 = private unnamed_addr constant [24 x i8] c"implicit_truncation.err\00", align 1, !dbg !178
@.str.43 = private unnamed_addr constant [24 x i8] c"implicit_conversion.err\00", align 1, !dbg !180
@.str.44 = private unnamed_addr constant [21 x i8] c"unreachable_call.err\00", align 1, !dbg !182
@.str.45 = private unnamed_addr constant [19 x i8] c"missing_return.err\00", align 1, !dbg !184
@.str.46 = private unnamed_addr constant [17 x i8] c"invalid_load.err\00", align 1, !dbg !186
@.str.47 = private unnamed_addr constant [27 x i8] c"function_type_mismatch.err\00", align 1, !dbg !188
@.str.48 = private unnamed_addr constant [23 x i8] c"nullable_attribute.err\00", align 1, !dbg !191
@.str.49.52 = private unnamed_addr constant [26 x i8] c"integer division overflow\00", align 1, !dbg !193
@.str.50 = private unnamed_addr constant [20 x i8] c"shift out of bounds\00", align 1, !dbg !195
@.str.51 = private unnamed_addr constant [19 x i8] c"load invalid value\00", align 1, !dbg !197
@.str.57 = private unnamed_addr constant [8 x i8] c"IGNORED\00", align 1, !dbg !199
@.str.1.58 = private unnamed_addr constant [16 x i8] c"overshift error\00", align 1, !dbg !202
@.str.2.59 = private unnamed_addr constant [14 x i8] c"overshift.err\00", align 1, !dbg !207

; Function Attrs: noinline nounwind sspstrong uwtable
define i32 @permute(i32 noundef %0, ptr noundef %1, ptr noundef %2, ptr noundef %3, ptr noundef %4, ptr noundef %5, ptr noundef %6) #0 !dbg !329 {
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca ptr, align 8
  %11 = alloca ptr, align 8
  %12 = alloca ptr, align 8
  %13 = alloca ptr, align 8
  %14 = alloca ptr, align 8
  %15 = alloca ptr, align 8
  %16 = alloca i32, align 4
  %17 = alloca i32, align 4
  %18 = alloca i32, align 4
  %19 = alloca i32, align 4
  %20 = alloca i32, align 4
  %21 = alloca i32, align 4
  store i32 %0, ptr %9, align 4
    #dbg_declare(ptr %9, !335, !DIExpression(), !336)
  store ptr %1, ptr %10, align 8
    #dbg_declare(ptr %10, !337, !DIExpression(), !338)
  store ptr %2, ptr %11, align 8
    #dbg_declare(ptr %11, !339, !DIExpression(), !340)
  store ptr %3, ptr %12, align 8
    #dbg_declare(ptr %12, !341, !DIExpression(), !342)
  store ptr %4, ptr %13, align 8
    #dbg_declare(ptr %13, !343, !DIExpression(), !344)
  store ptr %5, ptr %14, align 8
    #dbg_declare(ptr %14, !345, !DIExpression(), !346)
  store ptr %6, ptr %15, align 8
    #dbg_declare(ptr %15, !347, !DIExpression(), !348)
    #dbg_declare(ptr %16, !349, !DIExpression(), !350)
    #dbg_declare(ptr %17, !351, !DIExpression(), !352)
    #dbg_declare(ptr %18, !353, !DIExpression(), !354)
    #dbg_declare(ptr %19, !355, !DIExpression(), !356)
    #dbg_declare(ptr %20, !357, !DIExpression(), !358)
    #dbg_declare(ptr %21, !359, !DIExpression(), !360)
  %22 = load ptr, ptr %15, align 8, !dbg !361
  %23 = getelementptr i32, ptr %22, i64 0, !dbg !362
  store i32 0, ptr %23, align 4, !dbg !362
  %24 = load ptr, ptr %15, align 8, !dbg !363
  %25 = getelementptr i32, ptr %24, i64 1, !dbg !364
  store i32 0, ptr %25, align 4, !dbg !364
  %26 = load ptr, ptr %15, align 8, !dbg !365
  %27 = getelementptr i32, ptr %26, i64 2, !dbg !366
  store i32 0, ptr %27, align 4, !dbg !366
  %28 = load i32, ptr %9, align 4, !dbg !367
  %29 = icmp ugt i32 %28, 1024, !dbg !369
  br i1 %29, label %30, label %31, !dbg !370

30:                                               ; preds = %7
  store i32 2, ptr %8, align 4, !dbg !371
  br label %305, !dbg !371

31:                                               ; preds = %7
  %32 = load i32, ptr %9, align 4, !dbg !373
  %33 = icmp eq i32 %32, 0, !dbg !375
  br i1 %33, label %34, label %35, !dbg !376

34:                                               ; preds = %31
  store i32 0, ptr %8, align 4, !dbg !377
  br label %305, !dbg !377

35:                                               ; preds = %31
  store i32 0, ptr %16, align 4, !dbg !379
  br label %36, !dbg !380

36:                                               ; preds = %35, %40
  %37 = load i32, ptr %16, align 4, !dbg !381
  %38 = load i32, ptr %9, align 4, !dbg !384
  %39 = icmp ult i32 %37, %38, !dbg !385
  br i1 %39, label %40, label %47, !dbg !386

40:                                               ; preds = %36
  %41 = load ptr, ptr %13, align 8, !dbg !387
  %42 = load i32, ptr %16, align 4, !dbg !388
  %43 = zext i32 %42 to i64, !dbg !389
  %44 = getelementptr i32, ptr %41, i64 %43, !dbg !389
  store i32 0, ptr %44, align 4, !dbg !389
  %45 = load i32, ptr %16, align 4, !dbg !390
  %46 = add i32 %45, 1, !dbg !391
  store i32 %46, ptr %16, align 4, !dbg !392
  br label %36, !dbg !380, !llvm.loop !393

47:                                               ; preds = %36
  store i32 0, ptr %16, align 4, !dbg !395
  br label %48, !dbg !396

48:                                               ; preds = %47, %70
  %49 = load i32, ptr %16, align 4, !dbg !397
  %50 = load i32, ptr %9, align 4, !dbg !400
  %51 = icmp ult i32 %49, %50, !dbg !401
  br i1 %51, label %52, label %86, !dbg !402

52:                                               ; preds = %48
  %53 = load ptr, ptr %11, align 8, !dbg !403
  %54 = load i32, ptr %16, align 4, !dbg !404
  %55 = zext i32 %54 to i64, !dbg !403
  %56 = getelementptr i32, ptr %53, i64 %55, !dbg !403
  %57 = load i32, ptr %56, align 4, !dbg !403
  store i32 %57, ptr %17, align 4, !dbg !405
  %58 = load i32, ptr %17, align 4, !dbg !406
  %59 = load i32, ptr %9, align 4, !dbg !408
  %60 = icmp uge i32 %58, %59, !dbg !409
  br i1 %60, label %61, label %62, !dbg !410

61:                                               ; preds = %52
  store i32 2, ptr %8, align 4, !dbg !411
  br label %305, !dbg !411

62:                                               ; preds = %52
  %63 = load ptr, ptr %13, align 8, !dbg !413
  %64 = load i32, ptr %17, align 4, !dbg !415
  %65 = zext i32 %64 to i64, !dbg !413
  %66 = getelementptr i32, ptr %63, i64 %65, !dbg !413
  %67 = load i32, ptr %66, align 4, !dbg !413
  %68 = icmp ne i32 %67, 0, !dbg !416
  br i1 %68, label %69, label %70, !dbg !417

69:                                               ; preds = %62
  store i32 2, ptr %8, align 4, !dbg !418
  br label %305, !dbg !418

70:                                               ; preds = %62
  %71 = load ptr, ptr %13, align 8, !dbg !420
  %72 = load i32, ptr %17, align 4, !dbg !421
  %73 = zext i32 %72 to i64, !dbg !422
  %74 = getelementptr i32, ptr %71, i64 %73, !dbg !422
  store i32 1, ptr %74, align 4, !dbg !422
  %75 = load ptr, ptr %10, align 8, !dbg !423
  %76 = load i32, ptr %16, align 4, !dbg !424
  %77 = zext i32 %76 to i64, !dbg !423
  %78 = getelementptr i32, ptr %75, i64 %77, !dbg !423
  %79 = load i32, ptr %78, align 4, !dbg !423
  %80 = load ptr, ptr %12, align 8, !dbg !425
  %81 = load i32, ptr %17, align 4, !dbg !426
  %82 = zext i32 %81 to i64, !dbg !427
  %83 = getelementptr i32, ptr %80, i64 %82, !dbg !427
  store i32 %79, ptr %83, align 4, !dbg !427
  %84 = load i32, ptr %16, align 4, !dbg !428
  %85 = add i32 %84, 1, !dbg !429
  store i32 %85, ptr %16, align 4, !dbg !430
  br label %48, !dbg !396, !llvm.loop !431

86:                                               ; preds = %48
  store i32 0, ptr %16, align 4, !dbg !433
  br label %87, !dbg !434

87:                                               ; preds = %86, %118
  %88 = load i32, ptr %16, align 4, !dbg !435
  %89 = load i32, ptr %9, align 4, !dbg !438
  %90 = icmp ult i32 %88, %89, !dbg !439
  br i1 %90, label %91, label %121, !dbg !440

91:                                               ; preds = %87
  %92 = load ptr, ptr %10, align 8, !dbg !441
  %93 = load i32, ptr %16, align 4, !dbg !443
  %94 = zext i32 %93 to i64, !dbg !441
  %95 = getelementptr i32, ptr %92, i64 %94, !dbg !441
  %96 = load i32, ptr %95, align 4, !dbg !441
  %97 = load ptr, ptr %12, align 8, !dbg !444
  %98 = load i32, ptr %16, align 4, !dbg !445
  %99 = zext i32 %98 to i64, !dbg !444
  %100 = getelementptr i32, ptr %97, i64 %99, !dbg !444
  %101 = load i32, ptr %100, align 4, !dbg !444
  %102 = icmp eq i32 %96, %101, !dbg !446
  br i1 %102, label %103, label %113, !dbg !447

103:                                              ; preds = %91
  %104 = load i32, ptr %16, align 4, !dbg !448
  %105 = load ptr, ptr %11, align 8, !dbg !450
  %106 = load i32, ptr %16, align 4, !dbg !451
  %107 = zext i32 %106 to i64, !dbg !452
  %108 = getelementptr i32, ptr %105, i64 %107, !dbg !452
  store i32 %104, ptr %108, align 4, !dbg !452
  %109 = load ptr, ptr %13, align 8, !dbg !453
  %110 = load i32, ptr %16, align 4, !dbg !454
  %111 = zext i32 %110 to i64, !dbg !455
  %112 = getelementptr i32, ptr %109, i64 %111, !dbg !455
  store i32 1, ptr %112, align 4, !dbg !455
  br label %118, !dbg !456

113:                                              ; preds = %91
  %114 = load ptr, ptr %13, align 8, !dbg !457
  %115 = load i32, ptr %16, align 4, !dbg !459
  %116 = zext i32 %115 to i64, !dbg !460
  %117 = getelementptr i32, ptr %114, i64 %116, !dbg !460
  store i32 0, ptr %117, align 4, !dbg !460
  br label %118

118:                                              ; preds = %113, %103
  %119 = load i32, ptr %16, align 4, !dbg !461
  %120 = add i32 %119, 1, !dbg !462
  store i32 %120, ptr %16, align 4, !dbg !463
  br label %87, !dbg !434, !llvm.loop !464

121:                                              ; preds = %87
  store i32 0, ptr %16, align 4, !dbg !466
  br label %122, !dbg !467

122:                                              ; preds = %121, %180
  %123 = load i32, ptr %16, align 4, !dbg !468
  %124 = load i32, ptr %9, align 4, !dbg !471
  %125 = icmp ult i32 %123, %124, !dbg !472
  br i1 %125, label %126, label %183, !dbg !473

126:                                              ; preds = %122
  %127 = load ptr, ptr %10, align 8, !dbg !474
  %128 = load i32, ptr %16, align 4, !dbg !476
  %129 = zext i32 %128 to i64, !dbg !474
  %130 = getelementptr i32, ptr %127, i64 %129, !dbg !474
  %131 = load i32, ptr %130, align 4, !dbg !474
  %132 = load ptr, ptr %12, align 8, !dbg !477
  %133 = load i32, ptr %16, align 4, !dbg !478
  %134 = zext i32 %133 to i64, !dbg !477
  %135 = getelementptr i32, ptr %132, i64 %134, !dbg !477
  %136 = load i32, ptr %135, align 4, !dbg !477
  %137 = icmp ne i32 %131, %136, !dbg !479
  br i1 %137, label %138, label %180, !dbg !480

138:                                              ; preds = %126
  store i32 0, ptr %17, align 4, !dbg !481
  br label %139, !dbg !483

139:                                              ; preds = %138, %162
  %140 = load i32, ptr %17, align 4, !dbg !484
  %141 = load i32, ptr %9, align 4, !dbg !487
  %142 = icmp ult i32 %140, %141, !dbg !488
  br i1 %142, label %143, label %165, !dbg !489

143:                                              ; preds = %139
  %144 = load ptr, ptr %13, align 8, !dbg !490
  %145 = load i32, ptr %17, align 4, !dbg !492
  %146 = zext i32 %145 to i64, !dbg !490
  %147 = getelementptr i32, ptr %144, i64 %146, !dbg !490
  %148 = load i32, ptr %147, align 4, !dbg !490
  %149 = icmp eq i32 %148, 0, !dbg !493
  br i1 %149, label %150, label %162, !dbg !494

150:                                              ; preds = %143
  %151 = load ptr, ptr %10, align 8, !dbg !495
  %152 = load i32, ptr %16, align 4, !dbg !498
  %153 = zext i32 %152 to i64, !dbg !495
  %154 = getelementptr i32, ptr %151, i64 %153, !dbg !495
  %155 = load i32, ptr %154, align 4, !dbg !495
  %156 = load ptr, ptr %12, align 8, !dbg !499
  %157 = load i32, ptr %17, align 4, !dbg !500
  %158 = zext i32 %157 to i64, !dbg !499
  %159 = getelementptr i32, ptr %156, i64 %158, !dbg !499
  %160 = load i32, ptr %159, align 4, !dbg !499
  %161 = icmp eq i32 %155, %160, !dbg !501
  br i1 %161, label %165, label %162, !dbg !502

162:                                              ; preds = %143, %150
  %163 = load i32, ptr %17, align 4, !dbg !503
  %164 = add i32 %163, 1, !dbg !504
  store i32 %164, ptr %17, align 4, !dbg !505
  br label %139, !dbg !483, !llvm.loop !506

165:                                              ; preds = %150, %139
  %166 = load i32, ptr %17, align 4, !dbg !508
  %167 = load i32, ptr %9, align 4, !dbg !510
  %168 = icmp eq i32 %166, %167, !dbg !511
  br i1 %168, label %169, label %170, !dbg !512

169:                                              ; preds = %165
  store i32 2, ptr %8, align 4, !dbg !513
  br label %305, !dbg !513

170:                                              ; preds = %165
  %171 = load i32, ptr %17, align 4, !dbg !515
  %172 = load ptr, ptr %11, align 8, !dbg !516
  %173 = load i32, ptr %16, align 4, !dbg !517
  %174 = zext i32 %173 to i64, !dbg !518
  %175 = getelementptr i32, ptr %172, i64 %174, !dbg !518
  store i32 %171, ptr %175, align 4, !dbg !518
  %176 = load ptr, ptr %13, align 8, !dbg !519
  %177 = load i32, ptr %17, align 4, !dbg !520
  %178 = zext i32 %177 to i64, !dbg !521
  %179 = getelementptr i32, ptr %176, i64 %178, !dbg !521
  store i32 1, ptr %179, align 4, !dbg !521
  br label %180, !dbg !522

180:                                              ; preds = %126, %170
  %181 = load i32, ptr %16, align 4, !dbg !523
  %182 = add i32 %181, 1, !dbg !524
  store i32 %182, ptr %16, align 4, !dbg !525
  br label %122, !dbg !467, !llvm.loop !526

183:                                              ; preds = %122
  %184 = load i32, ptr %9, align 4, !dbg !528
  %185 = sub i32 %184, 1, !dbg !529
  store i32 %185, ptr %18, align 4, !dbg !530
  br label %186, !dbg !531

186:                                              ; preds = %183, %285
  %187 = load ptr, ptr %11, align 8, !dbg !532
  %188 = load i32, ptr %18, align 4, !dbg !534
  %189 = zext i32 %188 to i64, !dbg !532
  %190 = getelementptr i32, ptr %187, i64 %189, !dbg !532
  %191 = load i32, ptr %190, align 4, !dbg !532
  store i32 %191, ptr %19, align 4, !dbg !535
  %192 = load i32, ptr %19, align 4, !dbg !536
  %193 = load i32, ptr %18, align 4, !dbg !538
  %194 = icmp eq i32 %192, %193, !dbg !539
  br i1 %194, label %195, label %217, !dbg !540

195:                                              ; preds = %186
  %.old = load i32, ptr %19, align 4, !dbg !541
  %.old1 = icmp ugt i32 %.old, 0, !dbg !545
  br i1 %.old1, label %196, label %208, !dbg !546

196:                                              ; preds = %196, %195
  %197 = load i32, ptr %19, align 4, !dbg !547
  %198 = sub i32 %197, 1, !dbg !548
  store i32 %198, ptr %19, align 4, !dbg !549
  %199 = load ptr, ptr %11, align 8, !dbg !550
  %200 = load i32, ptr %19, align 4, !dbg !552
  %201 = zext i32 %200 to i64, !dbg !550
  %202 = getelementptr i32, ptr %199, i64 %201, !dbg !550
  %203 = load i32, ptr %202, align 4, !dbg !550
  %204 = load i32, ptr %19, align 4, !dbg !553
  %205 = icmp eq i32 %203, %204, !dbg !554
  %206 = load i32, ptr %19, align 4
  %207 = icmp ugt i32 %206, 0
  %or.cond = select i1 %205, i1 %207, i1 false, !dbg !555
  br i1 %or.cond, label %196, label %208, !dbg !555, !llvm.loop !556

208:                                              ; preds = %196, %195
  %209 = load ptr, ptr %11, align 8, !dbg !559
  %210 = load i32, ptr %19, align 4, !dbg !561
  %211 = zext i32 %210 to i64, !dbg !559
  %212 = getelementptr i32, ptr %209, i64 %211, !dbg !559
  %213 = load i32, ptr %212, align 4, !dbg !559
  %214 = load i32, ptr %19, align 4, !dbg !562
  %215 = icmp eq i32 %213, %214, !dbg !563
  br i1 %215, label %216, label %217, !dbg !564

216:                                              ; preds = %208
  store i32 0, ptr %8, align 4, !dbg !565
  br label %305, !dbg !565

217:                                              ; preds = %186, %208
  %218 = load ptr, ptr %10, align 8, !dbg !567
  %219 = load i32, ptr %19, align 4, !dbg !569
  %220 = zext i32 %219 to i64, !dbg !567
  %221 = getelementptr i32, ptr %218, i64 %220, !dbg !567
  %222 = load i32, ptr %221, align 4, !dbg !567
  %223 = load ptr, ptr %10, align 8, !dbg !570
  %224 = load i32, ptr %18, align 4, !dbg !571
  %225 = zext i32 %224 to i64, !dbg !570
  %226 = getelementptr i32, ptr %223, i64 %225, !dbg !570
  %227 = load i32, ptr %226, align 4, !dbg !570
  %228 = icmp ne i32 %222, %227, !dbg !572
  br i1 %228, label %229, label %285, !dbg !573

229:                                              ; preds = %217
  %230 = load i32, ptr %18, align 4, !dbg !574
  %231 = load i32, ptr %19, align 4, !dbg !576
  %232 = sub i32 %230, %231, !dbg !577
  store i32 %232, ptr %21, align 4, !dbg !578
  %233 = load i32, ptr %21, align 4, !dbg !579
  %234 = icmp ugt i32 %233, 16, !dbg !581
  br i1 %234, label %235, label %243, !dbg !582

235:                                              ; preds = %229
  %236 = load i32, ptr %19, align 4, !dbg !583
  %237 = load ptr, ptr %15, align 8, !dbg !585
  %238 = getelementptr i32, ptr %237, i64 1, !dbg !586
  store i32 %236, ptr %238, align 4, !dbg !586
  %239 = load i32, ptr %21, align 4, !dbg !587
  %240 = sub i32 %239, 16, !dbg !588
  %241 = load ptr, ptr %15, align 8, !dbg !589
  %242 = getelementptr i32, ptr %241, i64 2, !dbg !590
  store i32 %240, ptr %242, align 4, !dbg !590
  store i32 1, ptr %8, align 4, !dbg !591
  br label %305, !dbg !591

243:                                              ; preds = %229
  %244 = load ptr, ptr %15, align 8, !dbg !592
  %245 = getelementptr i32, ptr %244, i64 0, !dbg !592
  %246 = load i32, ptr %245, align 4, !dbg !592
  %247 = load i32, ptr %9, align 4, !dbg !594
  %248 = load i32, ptr %9, align 4, !dbg !595
  %249 = add i32 %247, %248, !dbg !596
  %250 = icmp uge i32 %246, %249, !dbg !597
  br i1 %250, label %251, label %252, !dbg !598

251:                                              ; preds = %243
  store i32 2, ptr %8, align 4, !dbg !599
  br label %305, !dbg !599

252:                                              ; preds = %243
  %253 = load ptr, ptr %10, align 8, !dbg !601
  %254 = load i32, ptr %19, align 4, !dbg !602
  %255 = zext i32 %254 to i64, !dbg !601
  %256 = getelementptr i32, ptr %253, i64 %255, !dbg !601
  %257 = load i32, ptr %256, align 4, !dbg !601
  store i32 %257, ptr %20, align 4, !dbg !603
  %258 = load ptr, ptr %10, align 8, !dbg !604
  %259 = load i32, ptr %18, align 4, !dbg !605
  %260 = zext i32 %259 to i64, !dbg !604
  %261 = getelementptr i32, ptr %258, i64 %260, !dbg !604
  %262 = load i32, ptr %261, align 4, !dbg !604
  %263 = load ptr, ptr %10, align 8, !dbg !606
  %264 = load i32, ptr %19, align 4, !dbg !607
  %265 = zext i32 %264 to i64, !dbg !608
  %266 = getelementptr i32, ptr %263, i64 %265, !dbg !608
  store i32 %262, ptr %266, align 4, !dbg !608
  %267 = load i32, ptr %20, align 4, !dbg !609
  %268 = load ptr, ptr %10, align 8, !dbg !610
  %269 = load i32, ptr %18, align 4, !dbg !611
  %270 = zext i32 %269 to i64, !dbg !612
  %271 = getelementptr i32, ptr %268, i64 %270, !dbg !612
  store i32 %267, ptr %271, align 4, !dbg !612
  %272 = load i32, ptr %21, align 4, !dbg !613
  %273 = load ptr, ptr %14, align 8, !dbg !614
  %274 = load ptr, ptr %15, align 8, !dbg !615
  %275 = getelementptr i32, ptr %274, i64 0, !dbg !615
  %276 = load i32, ptr %275, align 4, !dbg !615
  %277 = zext i32 %276 to i64, !dbg !616
  %278 = getelementptr i32, ptr %273, i64 %277, !dbg !616
  store i32 %272, ptr %278, align 4, !dbg !616
  %279 = load ptr, ptr %15, align 8, !dbg !617
  %280 = getelementptr i32, ptr %279, i64 0, !dbg !617
  %281 = load i32, ptr %280, align 4, !dbg !617
  %282 = add i32 %281, 1, !dbg !618
  %283 = load ptr, ptr %15, align 8, !dbg !619
  %284 = getelementptr i32, ptr %283, i64 0, !dbg !620
  store i32 %282, ptr %284, align 4, !dbg !620
  br label %285, !dbg !621

285:                                              ; preds = %217, %252
  %286 = load ptr, ptr %11, align 8, !dbg !622
  %287 = load i32, ptr %19, align 4, !dbg !623
  %288 = zext i32 %287 to i64, !dbg !622
  %289 = getelementptr i32, ptr %286, i64 %288, !dbg !622
  %290 = load i32, ptr %289, align 4, !dbg !622
  store i32 %290, ptr %20, align 4, !dbg !624
  %291 = load ptr, ptr %11, align 8, !dbg !625
  %292 = load i32, ptr %18, align 4, !dbg !626
  %293 = zext i32 %292 to i64, !dbg !625
  %294 = getelementptr i32, ptr %291, i64 %293, !dbg !625
  %295 = load i32, ptr %294, align 4, !dbg !625
  %296 = load ptr, ptr %11, align 8, !dbg !627
  %297 = load i32, ptr %19, align 4, !dbg !628
  %298 = zext i32 %297 to i64, !dbg !629
  %299 = getelementptr i32, ptr %296, i64 %298, !dbg !629
  store i32 %295, ptr %299, align 4, !dbg !629
  %300 = load i32, ptr %20, align 4, !dbg !630
  %301 = load ptr, ptr %11, align 8, !dbg !631
  %302 = load i32, ptr %18, align 4, !dbg !632
  %303 = zext i32 %302 to i64, !dbg !633
  %304 = getelementptr i32, ptr %301, i64 %303, !dbg !633
  store i32 %300, ptr %304, align 4, !dbg !633
  br label %186, !dbg !531, !llvm.loop !634

305:                                              ; preds = %251, %235, %216, %169, %69, %61, %34, %30
  %306 = load i32, ptr %8, align 4, !dbg !636
  ret i32 %306, !dbg !636
}

; Function Attrs: noinline nounwind sspstrong uwtable
define i32 @checked_main() #0 !dbg !637 {
  %1 = alloca [39 x i32], align 16
  %2 = alloca [18 x i32], align 16
  %3 = alloca [18 x i32], align 16
  %4 = alloca [18 x i32], align 16
  %5 = alloca [18 x i32], align 16
  %6 = alloca [36 x i32], align 16
  %7 = alloca [3 x i32], align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
    #dbg_declare(ptr %1, !640, !DIExpression(), !644)
    #dbg_declare(ptr %2, !645, !DIExpression(), !647)
    #dbg_declare(ptr %3, !648, !DIExpression(), !649)
    #dbg_declare(ptr %4, !650, !DIExpression(), !651)
    #dbg_declare(ptr %5, !652, !DIExpression(), !653)
    #dbg_declare(ptr %6, !654, !DIExpression(), !658)
    #dbg_declare(ptr %7, !659, !DIExpression(), !663)
  %15 = getelementptr inbounds [39 x i32], ptr %1, i64 0, i64 0, !dbg !664
  call void @klee_make_symbolic(ptr noundef %15, i64 noundef 156, ptr noundef @.str), !dbg !665
    #dbg_declare(ptr %8, !666, !DIExpression(), !667)
  store i32 1, ptr %8, align 4, !dbg !667
    #dbg_declare(ptr %9, !668, !DIExpression(), !670)
  store i32 0, ptr %9, align 4, !dbg !670
  br label %16, !dbg !671

16:                                               ; preds = %146, %0
  %17 = load i32, ptr %9, align 4, !dbg !672
  %18 = icmp ult i32 %17, 18, !dbg !674
  br i1 %18, label %19, label %149, !dbg !675

19:                                               ; preds = %16
  %20 = load i32, ptr %9, align 4, !dbg !676
  %21 = zext i32 %20 to i64, !dbg !678, !nosanitize !334
  %22 = icmp ult i64 %21, 39, !dbg !678, !nosanitize !334
  br i1 %22, label %25, label %23, !dbg !678, !prof !679, !nosanitize !334

23:                                               ; preds = %19
  %24 = zext i32 %20 to i64, !dbg !678, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @2, i64 %24) #7, !dbg !678, !nosanitize !334
  unreachable, !dbg !678, !nosanitize !334

25:                                               ; preds = %19
  %26 = zext i32 %20 to i64, !dbg !678
  %27 = mul i64 %26, 4, !dbg !678
  %28 = add i64 0, %27, !dbg !678
  %29 = getelementptr [39 x i32], ptr %1, i64 0, i64 %26, !dbg !678
  %30 = sub i64 160, %28, !dbg !678
  %31 = icmp ult i64 160, %28, !dbg !678
  %32 = icmp ult i64 %30, 4, !dbg !678
  %33 = or i1 %31, %32, !dbg !678
  br i1 %33, label %308, label %34

34:                                               ; preds = %25
  %35 = load i32, ptr %29, align 4, !dbg !678
  %36 = icmp ult i32 %35, 18, !dbg !680
  %37 = zext i1 %36 to i32, !dbg !680
  %38 = load i32, ptr %8, align 4, !dbg !681
  %39 = and i32 %38, %37, !dbg !681
  store i32 %39, ptr %8, align 4, !dbg !681
    #dbg_declare(ptr %10, !682, !DIExpression(), !684)
  store i32 0, ptr %10, align 4, !dbg !684
  br label %40, !dbg !685

40:                                               ; preds = %75, %34
  %41 = load i32, ptr %10, align 4, !dbg !686
  %42 = load i32, ptr %9, align 4, !dbg !688
  %43 = icmp ult i32 %41, %42, !dbg !689
  br i1 %43, label %44, label %83, !dbg !690

44:                                               ; preds = %40
  %45 = load i32, ptr %9, align 4, !dbg !691
  %46 = zext i32 %45 to i64, !dbg !692, !nosanitize !334
  %47 = icmp ult i64 %46, 39, !dbg !692, !nosanitize !334
  br i1 %47, label %50, label %48, !dbg !692, !prof !679, !nosanitize !334

48:                                               ; preds = %44
  %49 = zext i32 %45 to i64, !dbg !692, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @3, i64 %49) #7, !dbg !692, !nosanitize !334
  unreachable, !dbg !692, !nosanitize !334

50:                                               ; preds = %44
  %51 = zext i32 %45 to i64, !dbg !692
  %52 = mul i64 %51, 4, !dbg !692
  %53 = add i64 0, %52, !dbg !692
  %54 = getelementptr [39 x i32], ptr %1, i64 0, i64 %51, !dbg !692
  %55 = sub i64 160, %53, !dbg !692
  %56 = icmp ult i64 160, %53, !dbg !692
  %57 = icmp ult i64 %55, 4, !dbg !692
  %58 = or i1 %56, %57, !dbg !692
  br i1 %58, label %309, label %59

59:                                               ; preds = %50
  %60 = load i32, ptr %54, align 4, !dbg !692
  %61 = load i32, ptr %10, align 4, !dbg !693
  %62 = zext i32 %61 to i64, !dbg !694, !nosanitize !334
  %63 = icmp ult i64 %62, 39, !dbg !694, !nosanitize !334
  br i1 %63, label %66, label %64, !dbg !694, !prof !679, !nosanitize !334

64:                                               ; preds = %59
  %65 = zext i32 %61 to i64, !dbg !694, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @4, i64 %65) #7, !dbg !694, !nosanitize !334
  unreachable, !dbg !694, !nosanitize !334

66:                                               ; preds = %59
  %67 = zext i32 %61 to i64, !dbg !694
  %68 = mul i64 %67, 4, !dbg !694
  %69 = add i64 0, %68, !dbg !694
  %70 = getelementptr [39 x i32], ptr %1, i64 0, i64 %67, !dbg !694
  %71 = sub i64 160, %69, !dbg !694
  %72 = icmp ult i64 160, %69, !dbg !694
  %73 = icmp ult i64 %71, 4, !dbg !694
  %74 = or i1 %72, %73, !dbg !694
  br i1 %74, label %310, label %75

75:                                               ; preds = %66
  %76 = load i32, ptr %70, align 4, !dbg !694
  %77 = icmp ne i32 %60, %76, !dbg !695
  %78 = zext i1 %77 to i32, !dbg !695
  %79 = load i32, ptr %8, align 4, !dbg !696
  %80 = and i32 %79, %78, !dbg !696
  store i32 %80, ptr %8, align 4, !dbg !696
  %81 = load i32, ptr %10, align 4, !dbg !697
  %82 = add i32 %81, 1, !dbg !697
  store i32 %82, ptr %10, align 4, !dbg !697
  br label %40, !dbg !698, !llvm.loop !699

83:                                               ; preds = %40
  %84 = load i32, ptr %9, align 4, !dbg !702
  %85 = zext i32 %84 to i64, !dbg !703, !nosanitize !334
  %86 = icmp ult i64 %85, 39, !dbg !703, !nosanitize !334
  br i1 %86, label %89, label %87, !dbg !703, !prof !679, !nosanitize !334

87:                                               ; preds = %83
  %88 = zext i32 %84 to i64, !dbg !703, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @5, i64 %88) #7, !dbg !703, !nosanitize !334
  unreachable, !dbg !703, !nosanitize !334

89:                                               ; preds = %83
  %90 = zext i32 %84 to i64, !dbg !703
  %91 = mul i64 %90, 4, !dbg !703
  %92 = add i64 0, %91, !dbg !703
  %93 = getelementptr [39 x i32], ptr %1, i64 0, i64 %90, !dbg !703
  %94 = sub i64 160, %92, !dbg !703
  %95 = icmp ult i64 160, %92, !dbg !703
  %96 = icmp ult i64 %94, 4, !dbg !703
  %97 = or i1 %95, %96, !dbg !703
  br i1 %97, label %311, label %98

98:                                               ; preds = %89
  %99 = load i32, ptr %93, align 4, !dbg !703
  %100 = load i32, ptr %9, align 4, !dbg !704
  %101 = zext i32 %100 to i64, !dbg !705, !nosanitize !334
  %102 = icmp ult i64 %101, 18, !dbg !705, !nosanitize !334
  br i1 %102, label %105, label %103, !dbg !705, !prof !679, !nosanitize !334

103:                                              ; preds = %98
  %104 = zext i32 %100 to i64, !dbg !705, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @7, i64 %104) #7, !dbg !705, !nosanitize !334
  unreachable, !dbg !705, !nosanitize !334

105:                                              ; preds = %98
  %106 = zext i32 %100 to i64, !dbg !705
  %107 = mul i64 %106, 4, !dbg !705
  %108 = add i64 0, %107, !dbg !705
  %109 = getelementptr [18 x i32], ptr %3, i64 0, i64 %106, !dbg !705
  %110 = sub i64 80, %108, !dbg !705
  %111 = icmp ult i64 80, %108, !dbg !705
  %112 = icmp ult i64 %110, 4, !dbg !705
  %113 = or i1 %111, %112, !dbg !705
  br i1 %113, label %312, label %114

114:                                              ; preds = %105
  store i32 %99, ptr %109, align 4, !dbg !705
  %115 = load i32, ptr %9, align 4, !dbg !706
  %116 = add i32 18, %115, !dbg !707
  %117 = zext i32 %116 to i64, !dbg !708, !nosanitize !334
  %118 = icmp ult i64 %117, 39, !dbg !708, !nosanitize !334
  br i1 %118, label %121, label %119, !dbg !708, !prof !679, !nosanitize !334

119:                                              ; preds = %114
  %120 = zext i32 %116 to i64, !dbg !708, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @8, i64 %120) #7, !dbg !708, !nosanitize !334
  unreachable, !dbg !708, !nosanitize !334

121:                                              ; preds = %114
  %122 = zext i32 %116 to i64, !dbg !708
  %123 = mul i64 %122, 4, !dbg !708
  %124 = add i64 0, %123, !dbg !708
  %125 = getelementptr [39 x i32], ptr %1, i64 0, i64 %122, !dbg !708
  %126 = sub i64 160, %124, !dbg !708
  %127 = icmp ult i64 160, %124, !dbg !708
  %128 = icmp ult i64 %126, 4, !dbg !708
  %129 = or i1 %127, %128, !dbg !708
  br i1 %129, label %313, label %130

130:                                              ; preds = %121
  %131 = load i32, ptr %125, align 4, !dbg !708
  %132 = load i32, ptr %9, align 4, !dbg !709
  %133 = zext i32 %132 to i64, !dbg !710, !nosanitize !334
  %134 = icmp ult i64 %133, 18, !dbg !710, !nosanitize !334
  br i1 %134, label %137, label %135, !dbg !710, !prof !679, !nosanitize !334

135:                                              ; preds = %130
  %136 = zext i32 %132 to i64, !dbg !710, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @9, i64 %136) #7, !dbg !710, !nosanitize !334
  unreachable, !dbg !710, !nosanitize !334

137:                                              ; preds = %130
  %138 = zext i32 %132 to i64, !dbg !710
  %139 = mul i64 %138, 4, !dbg !710
  %140 = add i64 0, %139, !dbg !710
  %141 = getelementptr [18 x i32], ptr %2, i64 0, i64 %138, !dbg !710
  %142 = sub i64 80, %140, !dbg !710
  %143 = icmp ult i64 80, %140, !dbg !710
  %144 = icmp ult i64 %142, 4, !dbg !710
  %145 = or i1 %143, %144, !dbg !710
  br i1 %145, label %314, label %146

146:                                              ; preds = %137
  store i32 %131, ptr %141, align 4, !dbg !710
  %147 = load i32, ptr %9, align 4, !dbg !711
  %148 = add i32 %147, 1, !dbg !711
  store i32 %148, ptr %9, align 4, !dbg !711
  br label %16, !dbg !712, !llvm.loop !713

149:                                              ; preds = %16
  %150 = load i32, ptr %8, align 4, !dbg !715
  %151 = icmp eq i32 %150, 0, !dbg !716
  %152 = zext i1 %151 to i32, !dbg !716
  %153 = sext i32 %152 to i64, !dbg !715
  call void @klee_assume(i64 noundef %153), !dbg !717
    #dbg_declare(ptr %11, !718, !DIExpression(), !720)
  store i32 0, ptr %11, align 4, !dbg !720
  br label %154, !dbg !721

154:                                              ; preds = %189, %149
  %155 = load i32, ptr %11, align 4, !dbg !722
  %156 = icmp ult i32 %155, 3, !dbg !724
  br i1 %156, label %157, label %192, !dbg !725

157:                                              ; preds = %154
  %158 = load i32, ptr %11, align 4, !dbg !726
  %159 = add i32 36, %158, !dbg !727
  %160 = zext i32 %159 to i64, !dbg !728, !nosanitize !334
  %161 = icmp ult i64 %160, 39, !dbg !728, !nosanitize !334
  br i1 %161, label %164, label %162, !dbg !728, !prof !679, !nosanitize !334

162:                                              ; preds = %157
  %163 = zext i32 %159 to i64, !dbg !728, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @10, i64 %163) #7, !dbg !728, !nosanitize !334
  unreachable, !dbg !728, !nosanitize !334

164:                                              ; preds = %157
  %165 = zext i32 %159 to i64, !dbg !728
  %166 = mul i64 %165, 4, !dbg !728
  %167 = add i64 0, %166, !dbg !728
  %168 = getelementptr [39 x i32], ptr %1, i64 0, i64 %165, !dbg !728
  %169 = sub i64 160, %167, !dbg !728
  %170 = icmp ult i64 160, %167, !dbg !728
  %171 = icmp ult i64 %169, 4, !dbg !728
  %172 = or i1 %170, %171, !dbg !728
  br i1 %172, label %315, label %173

173:                                              ; preds = %164
  %174 = load i32, ptr %168, align 4, !dbg !728
  %175 = load i32, ptr %11, align 4, !dbg !729
  %176 = zext i32 %175 to i64, !dbg !730, !nosanitize !334
  %177 = icmp ult i64 %176, 3, !dbg !730, !nosanitize !334
  br i1 %177, label %180, label %178, !dbg !730, !prof !679, !nosanitize !334

178:                                              ; preds = %173
  %179 = zext i32 %175 to i64, !dbg !730, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @12, i64 %179) #7, !dbg !730, !nosanitize !334
  unreachable, !dbg !730, !nosanitize !334

180:                                              ; preds = %173
  %181 = zext i32 %175 to i64, !dbg !730
  %182 = mul i64 %181, 4, !dbg !730
  %183 = add i64 0, %182, !dbg !730
  %184 = getelementptr [3 x i32], ptr %7, i64 0, i64 %181, !dbg !730
  %185 = sub i64 12, %183, !dbg !730
  %186 = icmp ult i64 12, %183, !dbg !730
  %187 = icmp ult i64 %185, 4, !dbg !730
  %188 = or i1 %186, %187, !dbg !730
  br i1 %188, label %316, label %189

189:                                              ; preds = %180
  store i32 %174, ptr %184, align 4, !dbg !730
  %190 = load i32, ptr %11, align 4, !dbg !731
  %191 = add i32 %190, 1, !dbg !731
  store i32 %191, ptr %11, align 4, !dbg !731
  br label %154, !dbg !732, !llvm.loop !733

192:                                              ; preds = %154
    #dbg_declare(ptr %12, !735, !DIExpression(), !736)
  %193 = getelementptr inbounds [18 x i32], ptr %2, i64 0, i64 0, !dbg !737
  %194 = getelementptr inbounds [18 x i32], ptr %3, i64 0, i64 0, !dbg !738
  %195 = getelementptr inbounds [18 x i32], ptr %4, i64 0, i64 0, !dbg !739
  %196 = getelementptr inbounds [18 x i32], ptr %5, i64 0, i64 0, !dbg !740
  %197 = getelementptr inbounds [36 x i32], ptr %6, i64 0, i64 0, !dbg !741
  %198 = getelementptr inbounds [3 x i32], ptr %7, i64 0, i64 0, !dbg !742
  %199 = call i32 @permute(i32 noundef 18, ptr noundef %193, ptr noundef %194, ptr noundef %195, ptr noundef %196, ptr noundef %197, ptr noundef %198), !dbg !743
  store i32 %199, ptr %12, align 4, !dbg !736
  %200 = load i32, ptr %12, align 4, !dbg !744
  %201 = icmp eq i32 %200, 2, !dbg !744
  br i1 %201, label %203, label %202, !dbg !744

202:                                              ; preds = %192
  call void @klee_assert_fail(ptr noundef @.str.1, ptr noundef @.src, i32 noundef 37, ptr noundef @__PRETTY_FUNCTION__.checked_main) #8, !dbg !744
  unreachable, !dbg !744

203:                                              ; preds = %192
    #dbg_declare(ptr %13, !745, !DIExpression(), !747)
  store i32 0, ptr %13, align 4, !dbg !747
  br label %204, !dbg !748

204:                                              ; preds = %278, %203
  %205 = load i32, ptr %13, align 4, !dbg !749
  %206 = icmp ult i32 %205, 18, !dbg !751
  br i1 %206, label %207, label %281, !dbg !752

207:                                              ; preds = %204
  %208 = load i32, ptr %13, align 4, !dbg !753
  %209 = zext i32 %208 to i64, !dbg !753, !nosanitize !334
  %210 = icmp ult i64 %209, 18, !dbg !753, !nosanitize !334
  br i1 %210, label %213, label %211, !dbg !753, !prof !679, !nosanitize !334

211:                                              ; preds = %207
  %212 = zext i32 %208 to i64, !dbg !753, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @13, i64 %212) #7, !dbg !753, !nosanitize !334
  unreachable, !dbg !753, !nosanitize !334

213:                                              ; preds = %207
  %214 = zext i32 %208 to i64, !dbg !753
  %215 = mul i64 %214, 4, !dbg !753
  %216 = add i64 0, %215, !dbg !753
  %217 = getelementptr [18 x i32], ptr %3, i64 0, i64 %214, !dbg !753
  %218 = sub i64 80, %216, !dbg !753
  %219 = icmp ult i64 80, %216, !dbg !753
  %220 = icmp ult i64 %218, 4, !dbg !753
  %221 = or i1 %219, %220, !dbg !753
  br i1 %221, label %317, label %222

222:                                              ; preds = %213
  %223 = load i32, ptr %217, align 4, !dbg !753
  %224 = load i32, ptr %13, align 4, !dbg !753
  %225 = zext i32 %224 to i64, !dbg !753, !nosanitize !334
  %226 = icmp ult i64 %225, 39, !dbg !753, !nosanitize !334
  br i1 %226, label %229, label %227, !dbg !753, !prof !679, !nosanitize !334

227:                                              ; preds = %222
  %228 = zext i32 %224 to i64, !dbg !753, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @14, i64 %228) #7, !dbg !753, !nosanitize !334
  unreachable, !dbg !753, !nosanitize !334

229:                                              ; preds = %222
  %230 = zext i32 %224 to i64, !dbg !753
  %231 = mul i64 %230, 4, !dbg !753
  %232 = add i64 0, %231, !dbg !753
  %233 = getelementptr [39 x i32], ptr %1, i64 0, i64 %230, !dbg !753
  %234 = sub i64 160, %232, !dbg !753
  %235 = icmp ult i64 160, %232, !dbg !753
  %236 = icmp ult i64 %234, 4, !dbg !753
  %237 = or i1 %235, %236, !dbg !753
  br i1 %237, label %318, label %238

238:                                              ; preds = %229
  %239 = load i32, ptr %233, align 4, !dbg !753
  %240 = icmp eq i32 %223, %239, !dbg !753
  br i1 %240, label %242, label %241, !dbg !753

241:                                              ; preds = %238
  call void @klee_assert_fail(ptr noundef @.str.2, ptr noundef @.src, i32 noundef 39, ptr noundef @__PRETTY_FUNCTION__.checked_main) #8, !dbg !753
  unreachable, !dbg !753

242:                                              ; preds = %238
  %243 = load i32, ptr %13, align 4, !dbg !755
  %244 = zext i32 %243 to i64, !dbg !755, !nosanitize !334
  %245 = icmp ult i64 %244, 18, !dbg !755, !nosanitize !334
  br i1 %245, label %248, label %246, !dbg !755, !prof !679, !nosanitize !334

246:                                              ; preds = %242
  %247 = zext i32 %243 to i64, !dbg !755, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @15, i64 %247) #7, !dbg !755, !nosanitize !334
  unreachable, !dbg !755, !nosanitize !334

248:                                              ; preds = %242
  %249 = zext i32 %243 to i64, !dbg !755
  %250 = mul i64 %249, 4, !dbg !755
  %251 = add i64 0, %250, !dbg !755
  %252 = getelementptr [18 x i32], ptr %2, i64 0, i64 %249, !dbg !755
  %253 = sub i64 80, %251, !dbg !755
  %254 = icmp ult i64 80, %251, !dbg !755
  %255 = icmp ult i64 %253, 4, !dbg !755
  %256 = or i1 %254, %255, !dbg !755
  br i1 %256, label %319, label %257

257:                                              ; preds = %248
  %258 = load i32, ptr %252, align 4, !dbg !755
  %259 = load i32, ptr %13, align 4, !dbg !755
  %260 = add i32 18, %259, !dbg !755
  %261 = zext i32 %260 to i64, !dbg !755, !nosanitize !334
  %262 = icmp ult i64 %261, 39, !dbg !755, !nosanitize !334
  br i1 %262, label %265, label %263, !dbg !755, !prof !679, !nosanitize !334

263:                                              ; preds = %257
  %264 = zext i32 %260 to i64, !dbg !755, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @16, i64 %264) #7, !dbg !755, !nosanitize !334
  unreachable, !dbg !755, !nosanitize !334

265:                                              ; preds = %257
  %266 = zext i32 %260 to i64, !dbg !755
  %267 = mul i64 %266, 4, !dbg !755
  %268 = add i64 0, %267, !dbg !755
  %269 = getelementptr [39 x i32], ptr %1, i64 0, i64 %266, !dbg !755
  %270 = sub i64 160, %268, !dbg !755
  %271 = icmp ult i64 160, %268, !dbg !755
  %272 = icmp ult i64 %270, 4, !dbg !755
  %273 = or i1 %271, %272, !dbg !755
  br i1 %273, label %320, label %274

274:                                              ; preds = %265
  %275 = load i32, ptr %269, align 4, !dbg !755
  %276 = icmp eq i32 %258, %275, !dbg !755
  br i1 %276, label %278, label %277, !dbg !755

277:                                              ; preds = %274
  call void @klee_assert_fail(ptr noundef @.str.3, ptr noundef @.src, i32 noundef 40, ptr noundef @__PRETTY_FUNCTION__.checked_main) #8, !dbg !755
  unreachable, !dbg !755

278:                                              ; preds = %274
  %279 = load i32, ptr %13, align 4, !dbg !756
  %280 = add i32 %279, 1, !dbg !756
  store i32 %280, ptr %13, align 4, !dbg !756
  br label %204, !dbg !757, !llvm.loop !758

281:                                              ; preds = %204
    #dbg_declare(ptr %14, !760, !DIExpression(), !762)
  store i32 0, ptr %14, align 4, !dbg !762
  br label %282, !dbg !763

282:                                              ; preds = %304, %281
  %283 = load i32, ptr %14, align 4, !dbg !764
  %284 = icmp ult i32 %283, 3, !dbg !766
  br i1 %284, label %285, label %307, !dbg !767

285:                                              ; preds = %282
  %286 = load i32, ptr %14, align 4, !dbg !768
  %287 = zext i32 %286 to i64, !dbg !768, !nosanitize !334
  %288 = icmp ult i64 %287, 3, !dbg !768, !nosanitize !334
  br i1 %288, label %291, label %289, !dbg !768, !prof !679, !nosanitize !334

289:                                              ; preds = %285
  %290 = zext i32 %286 to i64, !dbg !768, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @17, i64 %290) #7, !dbg !768, !nosanitize !334
  unreachable, !dbg !768, !nosanitize !334

291:                                              ; preds = %285
  %292 = zext i32 %286 to i64, !dbg !768
  %293 = mul i64 %292, 4, !dbg !768
  %294 = add i64 0, %293, !dbg !768
  %295 = getelementptr [3 x i32], ptr %7, i64 0, i64 %292, !dbg !768
  %296 = sub i64 12, %294, !dbg !768
  %297 = icmp ult i64 12, %294, !dbg !768
  %298 = icmp ult i64 %296, 4, !dbg !768
  %299 = or i1 %297, %298, !dbg !768
  br i1 %299, label %321, label %300

300:                                              ; preds = %291
  %301 = load i32, ptr %295, align 4, !dbg !768
  %302 = icmp eq i32 %301, 0, !dbg !768
  br i1 %302, label %304, label %303, !dbg !768

303:                                              ; preds = %300
  call void @klee_assert_fail(ptr noundef @.str.4, ptr noundef @.src, i32 noundef 44, ptr noundef @__PRETTY_FUNCTION__.checked_main) #8, !dbg !768
  unreachable, !dbg !768

304:                                              ; preds = %300
  %305 = load i32, ptr %14, align 4, !dbg !769
  %306 = add i32 %305, 1, !dbg !769
  store i32 %306, ptr %14, align 4, !dbg !769
  br label %282, !dbg !770, !llvm.loop !771

307:                                              ; preds = %282
  ret i32 0, !dbg !773

308:                                              ; preds = %25
  call void @abort(), !dbg !678
  unreachable, !dbg !678

309:                                              ; preds = %50
  call void @abort(), !dbg !692
  unreachable, !dbg !692

310:                                              ; preds = %66
  call void @abort(), !dbg !694
  unreachable, !dbg !694

311:                                              ; preds = %89
  call void @abort(), !dbg !703
  unreachable, !dbg !703

312:                                              ; preds = %105
  call void @abort(), !dbg !705
  unreachable, !dbg !705

313:                                              ; preds = %121
  call void @abort(), !dbg !708
  unreachable, !dbg !708

314:                                              ; preds = %137
  call void @abort(), !dbg !710
  unreachable, !dbg !710

315:                                              ; preds = %164
  call void @abort(), !dbg !728
  unreachable, !dbg !728

316:                                              ; preds = %180
  call void @abort(), !dbg !730
  unreachable, !dbg !730

317:                                              ; preds = %213
  call void @abort(), !dbg !753
  unreachable, !dbg !753

318:                                              ; preds = %229
  call void @abort(), !dbg !753
  unreachable, !dbg !753

319:                                              ; preds = %248
  call void @abort(), !dbg !755
  unreachable, !dbg !755

320:                                              ; preds = %265
  call void @abort(), !dbg !755
  unreachable, !dbg !755

321:                                              ; preds = %291
  call void @abort(), !dbg !768
  unreachable, !dbg !768
}

declare void @klee_make_symbolic(ptr noundef, i64 noundef, ptr noundef) #1

declare void @klee_assume(i64 noundef) #1

; Function Attrs: noreturn
declare void @klee_assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2

; Function Attrs: noinline nounwind sspstrong uwtable
define i32 @main() #3 !dbg !774 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i8, align 1
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !775, !DIExpression(), !776)
  %4 = call i32 @checked_main(), !dbg !777
  store i32 %4, ptr %2, align 4, !dbg !776
    #dbg_declare(ptr %3, !778, !DIExpression(), !780)
  call void @klee_make_symbolic(ptr noundef %3, i64 noundef 1, ptr noundef @.str.5), !dbg !781
  %5 = load i32, ptr %2, align 4, !dbg !782
  ret i32 %5, !dbg !783
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_type_mismatch_v1(ptr noundef %0, i64 noundef %1) #4 !dbg !784 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !797, !DIExpression(), !798)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !799, !DIExpression(), !800)
  %5 = load ptr, ptr %3, align 8, !dbg !801
  %6 = load i64, ptr %4, align 8, !dbg !802
  call void @_ZN7__ubsanL22handleTypeMismatchImplEP16TypeMismatchDatam(ptr noundef %5, i64 noundef %6), !dbg !803
  ret void, !dbg !804
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL22handleTypeMismatchImplEP16TypeMismatchDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !805 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i64, align 8
  %6 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !806, !DIExpression(), !807)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !808, !DIExpression(), !809)
    #dbg_declare(ptr %5, !810, !DIExpression(), !811)
  %7 = load ptr, ptr %3, align 8, !dbg !812
  %8 = getelementptr inbounds %struct.TypeMismatchData, ptr %7, i32 0, i32 2, !dbg !813
  %9 = load i8, ptr %8, align 8, !dbg !813
  %10 = zext i8 %9 to i32, !dbg !812
  %11 = zext i32 %10 to i64, !dbg !814
  call void @klee_overshift_check(i64 64, i64 %11), !dbg !814
  %12 = shl i64 1, %11, !dbg !814, !klee.check.shift !815
  store i64 %12, ptr %5, align 8, !dbg !811
    #dbg_declare(ptr %6, !816, !DIExpression(), !817)
  %13 = load i64, ptr %4, align 8, !dbg !818
  %14 = icmp ne i64 %13, 0, !dbg !818
  br i1 %14, label %23, label %15, !dbg !820

15:                                               ; preds = %2
  %16 = load ptr, ptr %3, align 8, !dbg !821
  %17 = getelementptr inbounds %struct.TypeMismatchData, ptr %16, i32 0, i32 3, !dbg !822
  %18 = load i8, ptr %17, align 1, !dbg !822
  %19 = zext i8 %18 to i32, !dbg !821
  %20 = icmp eq i32 %19, 10, !dbg !823
  %21 = zext i1 %20 to i64, !dbg !824
  %22 = select i1 %20, i32 2, i32 1, !dbg !824
  store i32 %22, ptr %6, align 4, !dbg !825
  br label %31, !dbg !826

23:                                               ; preds = %2
  %24 = load i64, ptr %4, align 8, !dbg !827
  %25 = load i64, ptr %5, align 8, !dbg !829
  %26 = sub i64 %25, 1, !dbg !830
  %27 = and i64 %24, %26, !dbg !831
  %28 = icmp ne i64 %27, 0, !dbg !827
  br i1 %28, label %29, label %30, !dbg !832

29:                                               ; preds = %23
  store i32 7, ptr %6, align 4, !dbg !833
  br label %31, !dbg !834

30:                                               ; preds = %23
  store i32 9, ptr %6, align 4, !dbg !835
  br label %31

31:                                               ; preds = %29, %30, %15
  %32 = load i32, ptr %6, align 4, !dbg !836
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %32) #8, !dbg !837
  unreachable, !dbg !837
}

; Function Attrs: mustprogress noinline noreturn sspstrong uwtable
define internal void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %0) #5 !dbg !838 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !841, !DIExpression(), !842)
  %3 = load i32, ptr %2, align 4, !dbg !843
  %4 = call noundef ptr @_ZN7__ubsanL19ConvertTypeToStringENS_9ErrorTypeE(i32 noundef %3), !dbg !844
  %5 = load i32, ptr %2, align 4, !dbg !845
  %6 = call noundef ptr @_ZN7__ubsanL10get_suffixENS_9ErrorTypeE(i32 noundef %5), !dbg !846
  call void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef %4, ptr noundef %6) #8, !dbg !847
  unreachable, !dbg !847
}

; Function Attrs: mustprogress noinline nounwind sspstrong uwtable
define internal noundef ptr @_ZN7__ubsanL19ConvertTypeToStringENS_9ErrorTypeE(i32 noundef %0) #6 !dbg !848 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store i32 %0, ptr %3, align 4
    #dbg_declare(ptr %3, !851, !DIExpression(), !852)
  %4 = load i32, ptr %3, align 4, !dbg !853
  switch i32 %4, label %41 [
    i32 0, label %5
    i32 1, label %6
    i32 2, label %7
    i32 3, label %8
    i32 4, label %9
    i32 5, label %10
    i32 6, label %11
    i32 7, label %12
    i32 8, label %13
    i32 9, label %14
    i32 10, label %15
    i32 11, label %16
    i32 12, label %17
    i32 13, label %18
    i32 14, label %19
    i32 15, label %20
    i32 16, label %21
    i32 17, label %22
    i32 18, label %23
    i32 19, label %24
    i32 20, label %25
    i32 21, label %26
    i32 22, label %27
    i32 23, label %28
    i32 24, label %29
    i32 25, label %30
    i32 26, label %31
    i32 27, label %32
    i32 28, label %33
    i32 29, label %34
    i32 30, label %35
    i32 31, label %36
    i32 32, label %37
    i32 33, label %38
    i32 34, label %39
    i32 35, label %40
  ], !dbg !854

5:                                                ; preds = %1
  store ptr @.str.4.2, ptr %2, align 8, !dbg !855
  br label %42, !dbg !855

6:                                                ; preds = %1
  store ptr @.str.5.3, ptr %2, align 8, !dbg !858
  br label %42, !dbg !858

7:                                                ; preds = %1
  store ptr @.str.5.3, ptr %2, align 8, !dbg !859
  br label %42, !dbg !859

8:                                                ; preds = %1
  store ptr @.str.6, ptr %2, align 8, !dbg !860
  br label %42, !dbg !860

9:                                                ; preds = %1
  store ptr @.str.7, ptr %2, align 8, !dbg !861
  br label %42, !dbg !861

10:                                               ; preds = %1
  store ptr @.str.8, ptr %2, align 8, !dbg !862
  br label %42, !dbg !862

11:                                               ; preds = %1
  store ptr @.str.9, ptr %2, align 8, !dbg !863
  br label %42, !dbg !863

12:                                               ; preds = %1
  store ptr @.str.10, ptr %2, align 8, !dbg !864
  br label %42, !dbg !864

13:                                               ; preds = %1
  store ptr @.str.11, ptr %2, align 8, !dbg !865
  br label %42, !dbg !865

14:                                               ; preds = %1
  store ptr @.str.12, ptr %2, align 8, !dbg !866
  br label %42, !dbg !866

15:                                               ; preds = %1
  store ptr @.str.13, ptr %2, align 8, !dbg !867
  br label %42, !dbg !867

16:                                               ; preds = %1
  store ptr @.str.14, ptr %2, align 8, !dbg !868
  br label %42, !dbg !868

17:                                               ; preds = %1
  store ptr @.str.15, ptr %2, align 8, !dbg !869
  br label %42, !dbg !869

18:                                               ; preds = %1
  store ptr @.str.16, ptr %2, align 8, !dbg !870
  br label %42, !dbg !870

19:                                               ; preds = %1
  store ptr @.str.17, ptr %2, align 8, !dbg !871
  br label %42, !dbg !871

20:                                               ; preds = %1
  store ptr @.str.18, ptr %2, align 8, !dbg !872
  br label %42, !dbg !872

21:                                               ; preds = %1
  store ptr @.str.19, ptr %2, align 8, !dbg !873
  br label %42, !dbg !873

22:                                               ; preds = %1
  store ptr @.str.20, ptr %2, align 8, !dbg !874
  br label %42, !dbg !874

23:                                               ; preds = %1
  store ptr @.str.21, ptr %2, align 8, !dbg !875
  br label %42, !dbg !875

24:                                               ; preds = %1
  store ptr @.str.22, ptr %2, align 8, !dbg !876
  br label %42, !dbg !876

25:                                               ; preds = %1
  store ptr @.str.23, ptr %2, align 8, !dbg !877
  br label %42, !dbg !877

26:                                               ; preds = %1
  store ptr @.str.24, ptr %2, align 8, !dbg !878
  br label %42, !dbg !878

27:                                               ; preds = %1
  store ptr @.str.25, ptr %2, align 8, !dbg !879
  br label %42, !dbg !879

28:                                               ; preds = %1
  store ptr @.str.26, ptr %2, align 8, !dbg !880
  br label %42, !dbg !880

29:                                               ; preds = %1
  store ptr @.str.27, ptr %2, align 8, !dbg !881
  br label %42, !dbg !881

30:                                               ; preds = %1
  store ptr @.str.28, ptr %2, align 8, !dbg !882
  br label %42, !dbg !882

31:                                               ; preds = %1
  store ptr @.str.29, ptr %2, align 8, !dbg !883
  br label %42, !dbg !883

32:                                               ; preds = %1
  store ptr @.str.30, ptr %2, align 8, !dbg !884
  br label %42, !dbg !884

33:                                               ; preds = %1
  store ptr @.str.31, ptr %2, align 8, !dbg !885
  br label %42, !dbg !885

34:                                               ; preds = %1
  store ptr @.str.32, ptr %2, align 8, !dbg !886
  br label %42, !dbg !886

35:                                               ; preds = %1
  store ptr @.str.33, ptr %2, align 8, !dbg !887
  br label %42, !dbg !887

36:                                               ; preds = %1
  store ptr @.str.33, ptr %2, align 8, !dbg !888
  br label %42, !dbg !888

37:                                               ; preds = %1
  store ptr @.str.34, ptr %2, align 8, !dbg !889
  br label %42, !dbg !889

38:                                               ; preds = %1
  store ptr @.str.34, ptr %2, align 8, !dbg !890
  br label %42, !dbg !890

39:                                               ; preds = %1
  store ptr @.str.35, ptr %2, align 8, !dbg !891
  br label %42, !dbg !891

40:                                               ; preds = %1
  store ptr @.str.36, ptr %2, align 8, !dbg !892
  br label %42, !dbg !892

41:                                               ; preds = %1
  call void @abort(), !dbg !893
  unreachable, !dbg !893

42:                                               ; preds = %40, %39, %38, %37, %36, %35, %34, %33, %32, %31, %30, %29, %28, %27, %26, %25, %24, %23, %22, %21, %20, %19, %18, %17, %16, %15, %14, %13, %12, %11, %10, %9, %8, %7, %6, %5
  %43 = load ptr, ptr %2, align 8, !dbg !895
  ret ptr %43, !dbg !895
}

; Function Attrs: mustprogress noinline nounwind sspstrong uwtable
define internal noundef ptr @_ZN7__ubsanL10get_suffixENS_9ErrorTypeE(i32 noundef %0) #6 !dbg !896 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store i32 %0, ptr %3, align 4
    #dbg_declare(ptr %3, !897, !DIExpression(), !898)
  %4 = load i32, ptr %3, align 4, !dbg !899
  switch i32 %4, label %24 [
    i32 0, label %5
    i32 1, label %6
    i32 2, label %6
    i32 3, label %6
    i32 4, label %6
    i32 5, label %6
    i32 6, label %6
    i32 7, label %6
    i32 8, label %6
    i32 9, label %7
    i32 10, label %8
    i32 11, label %8
    i32 12, label %9
    i32 13, label %9
    i32 14, label %10
    i32 15, label %11
    i32 16, label %12
    i32 17, label %12
    i32 18, label %13
    i32 19, label %13
    i32 20, label %14
    i32 21, label %14
    i32 22, label %15
    i32 23, label %16
    i32 24, label %17
    i32 25, label %18
    i32 26, label %19
    i32 27, label %20
    i32 28, label %20
    i32 29, label %21
    i32 30, label %22
    i32 31, label %22
    i32 32, label %22
    i32 33, label %22
    i32 34, label %23
    i32 35, label %23
  ], !dbg !900

5:                                                ; preds = %1
  store ptr @.str.37, ptr %2, align 8, !dbg !901
  br label %25, !dbg !901

6:                                                ; preds = %1, %1, %1, %1, %1, %1, %1, %1
  store ptr @.str.38, ptr %2, align 8, !dbg !903
  br label %25, !dbg !903

7:                                                ; preds = %1
  store ptr @.str.38, ptr %2, align 8, !dbg !904
  br label %25, !dbg !904

8:                                                ; preds = %1, %1
  store ptr @.str.39, ptr %2, align 8, !dbg !905
  br label %25, !dbg !905

9:                                                ; preds = %1, %1
  store ptr @.str.40, ptr %2, align 8, !dbg !906
  br label %25, !dbg !906

10:                                               ; preds = %1
  store ptr @.str.41, ptr %2, align 8, !dbg !907
  br label %25, !dbg !907

11:                                               ; preds = %1
  store ptr @.str.37, ptr %2, align 8, !dbg !908
  br label %25, !dbg !908

12:                                               ; preds = %1, %1
  store ptr @.str.42, ptr %2, align 8, !dbg !909
  br label %25, !dbg !909

13:                                               ; preds = %1, %1
  store ptr @.str.43, ptr %2, align 8, !dbg !910
  br label %25, !dbg !910

14:                                               ; preds = %1, %1
  store ptr @.str.39, ptr %2, align 8, !dbg !911
  br label %25, !dbg !911

15:                                               ; preds = %1
  store ptr @.str.38, ptr %2, align 8, !dbg !912
  br label %25, !dbg !912

16:                                               ; preds = %1
  store ptr @.str.44, ptr %2, align 8, !dbg !913
  br label %25, !dbg !913

17:                                               ; preds = %1
  store ptr @.str.45, ptr %2, align 8, !dbg !914
  br label %25, !dbg !914

18:                                               ; preds = %1
  store ptr @.str.38, ptr %2, align 8, !dbg !915
  br label %25, !dbg !915

19:                                               ; preds = %1
  store ptr @.str.39, ptr %2, align 8, !dbg !916
  br label %25, !dbg !916

20:                                               ; preds = %1, %1
  store ptr @.str.46, ptr %2, align 8, !dbg !917
  br label %25, !dbg !917

21:                                               ; preds = %1
  store ptr @.str.47, ptr %2, align 8, !dbg !918
  br label %25, !dbg !918

22:                                               ; preds = %1, %1, %1, %1
  store ptr @.str.48, ptr %2, align 8, !dbg !919
  br label %25, !dbg !919

23:                                               ; preds = %1, %1
  store ptr @.str.37, ptr %2, align 8, !dbg !920
  br label %25, !dbg !920

24:                                               ; preds = %1
  store ptr @.str.37, ptr %2, align 8, !dbg !921
  br label %25, !dbg !921

25:                                               ; preds = %24, %23, %22, %21, %20, %19, %18, %17, %16, %15, %14, %13, %12, %11, %10, %9, %8, %7, %6, %5
  %26 = load ptr, ptr %2, align 8, !dbg !922
  ret ptr %26, !dbg !922
}

; Function Attrs: mustprogress noinline noreturn sspstrong uwtable
define internal void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef %0, ptr noundef %1) #5 !dbg !923 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !926, !DIExpression(), !927)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !928, !DIExpression(), !929)
  %5 = load ptr, ptr %3, align 8, !dbg !930
  %6 = load ptr, ptr %4, align 8, !dbg !931
  call void @klee_report_error(ptr noundef @.str.3.1, i32 noundef 37, ptr noundef %5, ptr noundef %6) #8, !dbg !932
  unreachable, !dbg !932
}

; Function Attrs: noreturn
declare void @klee_report_error(ptr noundef, i32 noundef, ptr noundef, ptr noundef) #2

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_type_mismatch_v1_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !933 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !934, !DIExpression(), !935)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !936, !DIExpression(), !937)
  %5 = load ptr, ptr %3, align 8, !dbg !938
  %6 = load i64, ptr %4, align 8, !dbg !939
  call void @_ZN7__ubsanL22handleTypeMismatchImplEP16TypeMismatchDatam(ptr noundef %5, i64 noundef %6), !dbg !940
  ret void, !dbg !941
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_alignment_assumption(ptr noundef %0, i64 noundef %1, i64 noundef %2, i64 noundef %3) #4 !dbg !942 {
  %5 = alloca ptr, align 8
  %6 = alloca i64, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  store ptr %0, ptr %5, align 8
    #dbg_declare(ptr %5, !947, !DIExpression(), !948)
  store i64 %1, ptr %6, align 8
    #dbg_declare(ptr %6, !949, !DIExpression(), !950)
  store i64 %2, ptr %7, align 8
    #dbg_declare(ptr %7, !951, !DIExpression(), !952)
  store i64 %3, ptr %8, align 8
    #dbg_declare(ptr %8, !953, !DIExpression(), !954)
  %9 = load ptr, ptr %5, align 8, !dbg !955
  %10 = load i64, ptr %6, align 8, !dbg !956
  %11 = load i64, ptr %7, align 8, !dbg !957
  %12 = load i64, ptr %8, align 8, !dbg !958
  call void @_ZN7__ubsanL29handleAlignmentAssumptionImplEP23AlignmentAssumptionDatammm(ptr noundef %9, i64 noundef %10, i64 noundef %11, i64 noundef %12), !dbg !959
  ret void, !dbg !960
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL29handleAlignmentAssumptionImplEP23AlignmentAssumptionDatammm(ptr noundef %0, i64 noundef %1, i64 noundef %2, i64 noundef %3) #4 !dbg !961 {
  %5 = alloca ptr, align 8
  %6 = alloca i64, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  %9 = alloca i32, align 4
  store ptr %0, ptr %5, align 8
    #dbg_declare(ptr %5, !962, !DIExpression(), !963)
  store i64 %1, ptr %6, align 8
    #dbg_declare(ptr %6, !964, !DIExpression(), !965)
  store i64 %2, ptr %7, align 8
    #dbg_declare(ptr %7, !966, !DIExpression(), !967)
  store i64 %3, ptr %8, align 8
    #dbg_declare(ptr %8, !968, !DIExpression(), !969)
    #dbg_declare(ptr %9, !970, !DIExpression(), !971)
  store i32 8, ptr %9, align 4, !dbg !971
  %10 = load i32, ptr %9, align 4, !dbg !972
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %10) #8, !dbg !973
  unreachable, !dbg !973
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_alignment_assumption_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2, i64 noundef %3) #4 !dbg !974 {
  %5 = alloca ptr, align 8
  %6 = alloca i64, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  store ptr %0, ptr %5, align 8
    #dbg_declare(ptr %5, !975, !DIExpression(), !976)
  store i64 %1, ptr %6, align 8
    #dbg_declare(ptr %6, !977, !DIExpression(), !978)
  store i64 %2, ptr %7, align 8
    #dbg_declare(ptr %7, !979, !DIExpression(), !980)
  store i64 %3, ptr %8, align 8
    #dbg_declare(ptr %8, !981, !DIExpression(), !982)
  %9 = load ptr, ptr %5, align 8, !dbg !983
  %10 = load i64, ptr %6, align 8, !dbg !984
  %11 = load i64, ptr %7, align 8, !dbg !985
  %12 = load i64, ptr %8, align 8, !dbg !986
  call void @_ZN7__ubsanL29handleAlignmentAssumptionImplEP23AlignmentAssumptionDatammm(ptr noundef %9, i64 noundef %10, i64 noundef %11, i64 noundef %12), !dbg !987
  ret void, !dbg !988
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_add_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !989 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !997, !DIExpression(), !998)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !999, !DIExpression(), !998)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1000, !DIExpression(), !998)
  %7 = load ptr, ptr %4, align 8, !dbg !998
  %8 = load i64, ptr %5, align 8, !dbg !998
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.49), !dbg !998
  ret void, !dbg !998
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %0, i64 noundef %1, ptr noundef %2) #4 !dbg !1001 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca ptr, align 8
  %7 = alloca i8, align 1
  %8 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1004, !DIExpression(), !1005)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1006, !DIExpression(), !1007)
  store ptr %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1008, !DIExpression(), !1009)
    #dbg_declare(ptr %7, !1010, !DIExpression(), !1011)
  %9 = load ptr, ptr %4, align 8, !dbg !1012
  %10 = getelementptr inbounds %struct.OverflowData, ptr %9, i32 0, i32 1, !dbg !1013
  %11 = load ptr, ptr %10, align 8, !dbg !1013
  %12 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %11), !dbg !1014
  %13 = zext i1 %12 to i8, !dbg !1011
  store i8 %13, ptr %7, align 1, !dbg !1011
    #dbg_declare(ptr %8, !1015, !DIExpression(), !1016)
  %14 = load i8, ptr %7, align 1, !dbg !1017
  %15 = trunc i8 %14 to i1, !dbg !1017
  %16 = zext i1 %15 to i64, !dbg !1017
  %17 = select i1 %15, i32 10, i32 11, !dbg !1017
  store i32 %17, ptr %8, align 4, !dbg !1016
  %18 = load i32, ptr %8, align 4, !dbg !1018
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %18) #8, !dbg !1019
  unreachable, !dbg !1019
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define linkonce_odr noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %0) #4 comdat align 2 !dbg !1020 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1021, !DIExpression(), !1023)
  %3 = load ptr, ptr %2, align 8
  %4 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %3), !dbg !1024
  br i1 %4, label %5, label %11, !dbg !1025

5:                                                ; preds = %1
  %6 = getelementptr inbounds %"class.__ubsan::TypeDescriptor", ptr %3, i32 0, i32 1, !dbg !1026
  %7 = load i16, ptr %6, align 2, !dbg !1026
  %8 = zext i16 %7 to i32, !dbg !1026
  %9 = and i32 %8, 1, !dbg !1027
  %10 = icmp ne i32 %9, 0, !dbg !1028
  br label %11

11:                                               ; preds = %5, %1
  %12 = phi i1 [ false, %1 ], [ %10, %5 ], !dbg !1023
  ret i1 %12, !dbg !1029
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define linkonce_odr noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %0) #4 comdat align 2 !dbg !1030 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1031, !DIExpression(), !1032)
  %3 = load ptr, ptr %2, align 8
  %4 = call noundef i32 @_ZNK7__ubsan14TypeDescriptor7getKindEv(ptr noundef nonnull align 2 dereferenceable(5) %3), !dbg !1033
  %5 = icmp eq i32 %4, 0, !dbg !1034
  ret i1 %5, !dbg !1035
}

; Function Attrs: mustprogress noinline nounwind sspstrong uwtable
define linkonce_odr noundef i32 @_ZNK7__ubsan14TypeDescriptor7getKindEv(ptr noundef nonnull align 2 dereferenceable(5) %0) #6 comdat align 2 !dbg !1036 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1037, !DIExpression(), !1038)
  %3 = load ptr, ptr %2, align 8
  %4 = getelementptr inbounds %"class.__ubsan::TypeDescriptor", ptr %3, i32 0, i32 0, !dbg !1039
  %5 = load i16, ptr %4, align 2, !dbg !1039
  %6 = zext i16 %5 to i32, !dbg !1040
  ret i32 %6, !dbg !1041
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_add_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1042 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1043, !DIExpression(), !1044)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1045, !DIExpression(), !1044)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1046, !DIExpression(), !1044)
  %7 = load ptr, ptr %4, align 8, !dbg !1044
  %8 = load i64, ptr %5, align 8, !dbg !1044
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.49), !dbg !1044
  ret void, !dbg !1044
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_sub_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1047 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1048, !DIExpression(), !1049)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1050, !DIExpression(), !1049)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1051, !DIExpression(), !1049)
  %7 = load ptr, ptr %4, align 8, !dbg !1049
  %8 = load i64, ptr %5, align 8, !dbg !1049
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.1.50), !dbg !1049
  ret void, !dbg !1049
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_sub_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1052 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1053, !DIExpression(), !1054)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1055, !DIExpression(), !1054)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1056, !DIExpression(), !1054)
  %7 = load ptr, ptr %4, align 8, !dbg !1054
  %8 = load i64, ptr %5, align 8, !dbg !1054
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.1.50), !dbg !1054
  ret void, !dbg !1054
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_mul_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1057 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1058, !DIExpression(), !1059)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1060, !DIExpression(), !1059)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1061, !DIExpression(), !1059)
  %7 = load ptr, ptr %4, align 8, !dbg !1059
  %8 = load i64, ptr %5, align 8, !dbg !1059
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.2.51), !dbg !1059
  ret void, !dbg !1059
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_mul_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1062 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1063, !DIExpression(), !1064)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1065, !DIExpression(), !1064)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1066, !DIExpression(), !1064)
  %7 = load ptr, ptr %4, align 8, !dbg !1064
  %8 = load i64, ptr %5, align 8, !dbg !1064
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.2.51), !dbg !1064
  ret void, !dbg !1064
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_negate_overflow(ptr noundef %0, i64 noundef %1) #4 !dbg !1067 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1070, !DIExpression(), !1071)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1072, !DIExpression(), !1073)
  %5 = load ptr, ptr %3, align 8, !dbg !1074
  %6 = load i64, ptr %4, align 8, !dbg !1075
  call void @_ZN7__ubsanL24handleNegateOverflowImplEP12OverflowDatam(ptr noundef %5, i64 noundef %6), !dbg !1076
  ret void, !dbg !1077
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL24handleNegateOverflowImplEP12OverflowDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1078 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i8, align 1
  %6 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1079, !DIExpression(), !1080)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1081, !DIExpression(), !1082)
    #dbg_declare(ptr %5, !1083, !DIExpression(), !1084)
  %7 = load ptr, ptr %3, align 8, !dbg !1085
  %8 = getelementptr inbounds %struct.OverflowData, ptr %7, i32 0, i32 1, !dbg !1086
  %9 = load ptr, ptr %8, align 8, !dbg !1086
  %10 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %9), !dbg !1087
  %11 = zext i1 %10 to i8, !dbg !1084
  store i8 %11, ptr %5, align 1, !dbg !1084
    #dbg_declare(ptr %6, !1088, !DIExpression(), !1089)
  %12 = load i8, ptr %5, align 1, !dbg !1090
  %13 = trunc i8 %12 to i1, !dbg !1090
  %14 = zext i1 %13 to i64, !dbg !1090
  %15 = select i1 %13, i32 10, i32 11, !dbg !1090
  store i32 %15, ptr %6, align 4, !dbg !1089
  %16 = load i32, ptr %6, align 4, !dbg !1091
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %16) #8, !dbg !1092
  unreachable, !dbg !1092
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_negate_overflow_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1093 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1094, !DIExpression(), !1095)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1096, !DIExpression(), !1097)
  %5 = load ptr, ptr %3, align 8, !dbg !1098
  %6 = load i64, ptr %4, align 8, !dbg !1099
  call void @_ZN7__ubsanL24handleNegateOverflowImplEP12OverflowDatam(ptr noundef %5, i64 noundef %6), !dbg !1100
  ret void, !dbg !1101
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_divrem_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1102 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1103, !DIExpression(), !1104)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1105, !DIExpression(), !1106)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1107, !DIExpression(), !1108)
  %7 = load ptr, ptr %4, align 8, !dbg !1109
  %8 = load i64, ptr %5, align 8, !dbg !1110
  %9 = load i64, ptr %6, align 8, !dbg !1111
  call void @_ZN7__ubsanL24handleDivremOverflowImplEP12OverflowDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1112
  ret void, !dbg !1113
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL24handleDivremOverflowImplEP12OverflowDatamm(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1114 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  %7 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1115, !DIExpression(), !1116)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1117, !DIExpression(), !1118)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1119, !DIExpression(), !1120)
  %8 = load ptr, ptr %4, align 8, !dbg !1121
  %9 = getelementptr inbounds %struct.OverflowData, ptr %8, i32 0, i32 1, !dbg !1123
  %10 = load ptr, ptr %9, align 8, !dbg !1123
  %11 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %10), !dbg !1124
  br i1 %11, label %12, label %13, !dbg !1125

12:                                               ; preds = %3
  call void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef @.str.49.52, ptr noundef @.str.39) #8, !dbg !1126
  unreachable, !dbg !1126

13:                                               ; preds = %3
    #dbg_declare(ptr %7, !1127, !DIExpression(), !1129)
  store i32 13, ptr %7, align 4, !dbg !1129
  %14 = load i32, ptr %7, align 4, !dbg !1130
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %14) #8, !dbg !1131
  unreachable, !dbg !1131
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_divrem_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1132 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1133, !DIExpression(), !1134)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1135, !DIExpression(), !1136)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1137, !DIExpression(), !1138)
  %7 = load ptr, ptr %4, align 8, !dbg !1139
  %8 = load i64, ptr %5, align 8, !dbg !1140
  %9 = load i64, ptr %6, align 8, !dbg !1141
  call void @_ZN7__ubsanL24handleDivremOverflowImplEP12OverflowDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1142
  ret void, !dbg !1143
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_shift_out_of_bounds(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1144 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1149, !DIExpression(), !1150)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1151, !DIExpression(), !1152)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1153, !DIExpression(), !1154)
  %7 = load ptr, ptr %4, align 8, !dbg !1155
  %8 = load i64, ptr %5, align 8, !dbg !1156
  %9 = load i64, ptr %6, align 8, !dbg !1157
  call void @_ZN7__ubsanL26handleShiftOutOfBoundsImplEP20ShiftOutOfBoundsDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1158
  ret void, !dbg !1159
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL26handleShiftOutOfBoundsImplEP20ShiftOutOfBoundsDatamm(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1160 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1161, !DIExpression(), !1162)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1163, !DIExpression(), !1164)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1165, !DIExpression(), !1166)
  call void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef @.str.50, ptr noundef @.str.39) #8, !dbg !1167
  unreachable, !dbg !1167
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_shift_out_of_bounds_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1168 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1169, !DIExpression(), !1170)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1171, !DIExpression(), !1172)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1173, !DIExpression(), !1174)
  %7 = load ptr, ptr %4, align 8, !dbg !1175
  %8 = load i64, ptr %5, align 8, !dbg !1176
  %9 = load i64, ptr %6, align 8, !dbg !1177
  call void @_ZN7__ubsanL26handleShiftOutOfBoundsImplEP20ShiftOutOfBoundsDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1178
  ret void, !dbg !1179
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_out_of_bounds(ptr noundef %0, i64 noundef %1) #4 !dbg !1180 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1185, !DIExpression(), !1186)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1187, !DIExpression(), !1188)
  %5 = load ptr, ptr %3, align 8, !dbg !1189
  %6 = load i64, ptr %4, align 8, !dbg !1190
  call void @_ZN7__ubsanL21handleOutOfBoundsImplEP15OutOfBoundsDatam(ptr noundef %5, i64 noundef %6), !dbg !1191
  ret void, !dbg !1192
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL21handleOutOfBoundsImplEP15OutOfBoundsDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1193 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1194, !DIExpression(), !1195)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1196, !DIExpression(), !1197)
    #dbg_declare(ptr %5, !1198, !DIExpression(), !1199)
  store i32 22, ptr %5, align 4, !dbg !1199
  %6 = load i32, ptr %5, align 4, !dbg !1200
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %6) #8, !dbg !1201
  unreachable, !dbg !1201
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_out_of_bounds_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1202 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1203, !DIExpression(), !1204)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1205, !DIExpression(), !1206)
  %5 = load ptr, ptr %3, align 8, !dbg !1207
  %6 = load i64, ptr %4, align 8, !dbg !1208
  call void @_ZN7__ubsanL21handleOutOfBoundsImplEP15OutOfBoundsDatam(ptr noundef %5, i64 noundef %6), !dbg !1209
  ret void, !dbg !1210
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_builtin_unreachable(ptr noundef %0) #4 !dbg !1211 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1216, !DIExpression(), !1217)
  %3 = load ptr, ptr %2, align 8, !dbg !1218
  call void @_ZN7__ubsanL28handleBuiltinUnreachableImplEP15UnreachableData(ptr noundef %3), !dbg !1219
  ret void, !dbg !1220
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL28handleBuiltinUnreachableImplEP15UnreachableData(ptr noundef %0) #4 !dbg !1221 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1222, !DIExpression(), !1223)
    #dbg_declare(ptr %3, !1224, !DIExpression(), !1225)
  store i32 23, ptr %3, align 4, !dbg !1225
  %4 = load i32, ptr %3, align 4, !dbg !1226
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %4) #8, !dbg !1227
  unreachable, !dbg !1227
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_missing_return(ptr noundef %0) #4 !dbg !1228 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1229, !DIExpression(), !1230)
  %3 = load ptr, ptr %2, align 8, !dbg !1231
  call void @_ZN7__ubsanL23handleMissingReturnImplEP15UnreachableData(ptr noundef %3), !dbg !1232
  ret void, !dbg !1233
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL23handleMissingReturnImplEP15UnreachableData(ptr noundef %0) #4 !dbg !1234 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1235, !DIExpression(), !1236)
    #dbg_declare(ptr %3, !1237, !DIExpression(), !1238)
  store i32 24, ptr %3, align 4, !dbg !1238
  %4 = load i32, ptr %3, align 4, !dbg !1239
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %4) #8, !dbg !1240
  unreachable, !dbg !1240
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_vla_bound_not_positive(ptr noundef %0, i64 noundef %1) #4 !dbg !1241 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1246, !DIExpression(), !1247)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1248, !DIExpression(), !1249)
  %5 = load ptr, ptr %3, align 8, !dbg !1250
  %6 = load i64, ptr %4, align 8, !dbg !1251
  call void @_ZN7__ubsanL25handleVLABoundNotPositiveEP12VLABoundDatam(ptr noundef %5, i64 noundef %6), !dbg !1252
  ret void, !dbg !1253
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL25handleVLABoundNotPositiveEP12VLABoundDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1254 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1255, !DIExpression(), !1256)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1257, !DIExpression(), !1258)
    #dbg_declare(ptr %5, !1259, !DIExpression(), !1260)
  store i32 25, ptr %5, align 4, !dbg !1260
  %6 = load i32, ptr %5, align 4, !dbg !1261
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %6) #8, !dbg !1262
  unreachable, !dbg !1262
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_vla_bound_not_positive_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1263 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1264, !DIExpression(), !1265)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1266, !DIExpression(), !1267)
  %5 = load ptr, ptr %3, align 8, !dbg !1268
  %6 = load i64, ptr %4, align 8, !dbg !1269
  call void @_ZN7__ubsanL25handleVLABoundNotPositiveEP12VLABoundDatam(ptr noundef %5, i64 noundef %6), !dbg !1270
  ret void, !dbg !1271
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_float_cast_overflow(ptr noundef %0, i64 noundef %1) #4 !dbg !1272 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1276, !DIExpression(), !1277)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1278, !DIExpression(), !1279)
  %5 = load ptr, ptr %3, align 8, !dbg !1280
  %6 = load i64, ptr %4, align 8, !dbg !1281
  call void @_ZN7__ubsanL23handleFloatCastOverflowEPvm(ptr noundef %5, i64 noundef %6), !dbg !1282
  ret void, !dbg !1283
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL23handleFloatCastOverflowEPvm(ptr noundef %0, i64 noundef %1) #4 !dbg !1284 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1285, !DIExpression(), !1286)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1287, !DIExpression(), !1288)
    #dbg_declare(ptr %5, !1289, !DIExpression(), !1290)
  store i32 26, ptr %5, align 4, !dbg !1290
  %6 = load i32, ptr %5, align 4, !dbg !1291
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %6) #8, !dbg !1292
  unreachable, !dbg !1292
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_float_cast_overflow_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1293 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1294, !DIExpression(), !1295)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1296, !DIExpression(), !1297)
  %5 = load ptr, ptr %3, align 8, !dbg !1298
  %6 = load i64, ptr %4, align 8, !dbg !1299
  call void @_ZN7__ubsanL23handleFloatCastOverflowEPvm(ptr noundef %5, i64 noundef %6), !dbg !1300
  ret void, !dbg !1301
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_load_invalid_value(ptr noundef %0, i64 noundef %1) #4 !dbg !1302 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1307, !DIExpression(), !1308)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1309, !DIExpression(), !1310)
  %5 = load ptr, ptr %3, align 8, !dbg !1311
  %6 = load i64, ptr %4, align 8, !dbg !1312
  call void @_ZN7__ubsanL22handleLoadInvalidValueEP16InvalidValueDatam(ptr noundef %5, i64 noundef %6), !dbg !1313
  ret void, !dbg !1314
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL22handleLoadInvalidValueEP16InvalidValueDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1315 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1316, !DIExpression(), !1317)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1318, !DIExpression(), !1319)
  call void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef @.str.51, ptr noundef @.str.46) #8, !dbg !1320
  unreachable, !dbg !1320
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_load_invalid_value_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1321 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1322, !DIExpression(), !1323)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1324, !DIExpression(), !1325)
  %5 = load ptr, ptr %3, align 8, !dbg !1326
  %6 = load i64, ptr %4, align 8, !dbg !1327
  call void @_ZN7__ubsanL22handleLoadInvalidValueEP16InvalidValueDatam(ptr noundef %5, i64 noundef %6), !dbg !1328
  ret void, !dbg !1329
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_implicit_conversion(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1330 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1340, !DIExpression(), !1341)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1342, !DIExpression(), !1343)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1344, !DIExpression(), !1345)
  %7 = load ptr, ptr %4, align 8, !dbg !1346
  %8 = load i64, ptr %5, align 8, !dbg !1347
  %9 = load i64, ptr %6, align 8, !dbg !1348
  call void @_ZN7__ubsanL24handleImplicitConversionEP22ImplicitConversionDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1349
  ret void, !dbg !1350
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL24handleImplicitConversionEP22ImplicitConversionDatamm(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1351 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  %7 = alloca i32, align 4
  %8 = alloca ptr, align 8
  %9 = alloca ptr, align 8
  %10 = alloca i8, align 1
  %11 = alloca i8, align 1
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1352, !DIExpression(), !1353)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1354, !DIExpression(), !1355)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1356, !DIExpression(), !1357)
    #dbg_declare(ptr %7, !1358, !DIExpression(), !1359)
  store i32 0, ptr %7, align 4, !dbg !1359
    #dbg_declare(ptr %8, !1360, !DIExpression(), !1361)
  %12 = load ptr, ptr %4, align 8, !dbg !1362
  %13 = getelementptr inbounds %struct.ImplicitConversionData, ptr %12, i32 0, i32 1, !dbg !1363
  %14 = load ptr, ptr %13, align 8, !dbg !1363
  store ptr %14, ptr %8, align 8, !dbg !1361
    #dbg_declare(ptr %9, !1364, !DIExpression(), !1365)
  %15 = load ptr, ptr %4, align 8, !dbg !1366
  %16 = getelementptr inbounds %struct.ImplicitConversionData, ptr %15, i32 0, i32 2, !dbg !1367
  %17 = load ptr, ptr %16, align 8, !dbg !1367
  store ptr %17, ptr %9, align 8, !dbg !1365
    #dbg_declare(ptr %10, !1368, !DIExpression(), !1369)
  %18 = load ptr, ptr %8, align 8, !dbg !1370
  %19 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %18), !dbg !1371
  %20 = zext i1 %19 to i8, !dbg !1369
  store i8 %20, ptr %10, align 1, !dbg !1369
    #dbg_declare(ptr %11, !1372, !DIExpression(), !1373)
  %21 = load ptr, ptr %9, align 8, !dbg !1374
  %22 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %21), !dbg !1375
  %23 = zext i1 %22 to i8, !dbg !1373
  store i8 %23, ptr %11, align 1, !dbg !1373
  %24 = load ptr, ptr %4, align 8, !dbg !1376
  %25 = getelementptr inbounds %struct.ImplicitConversionData, ptr %24, i32 0, i32 3, !dbg !1377
  %26 = load i8, ptr %25, align 8, !dbg !1377
  %27 = zext i8 %26 to i32, !dbg !1376
  switch i32 %27, label %40 [
    i32 0, label %28
    i32 1, label %36
    i32 2, label %37
    i32 3, label %38
    i32 4, label %39
  ], !dbg !1378

28:                                               ; preds = %3
  %29 = load i8, ptr %10, align 1, !dbg !1379
  %30 = trunc i8 %29 to i1, !dbg !1379
  br i1 %30, label %35, label %31, !dbg !1383

31:                                               ; preds = %28
  %32 = load i8, ptr %11, align 1, !dbg !1384
  %33 = trunc i8 %32 to i1, !dbg !1384
  br i1 %33, label %35, label %34, !dbg !1385

34:                                               ; preds = %31
  store i32 16, ptr %7, align 4, !dbg !1386
  br label %40, !dbg !1388

35:                                               ; preds = %31, %28
  store i32 17, ptr %7, align 4, !dbg !1389
  br label %40

36:                                               ; preds = %3
  store i32 16, ptr %7, align 4, !dbg !1391
  br label %40, !dbg !1392

37:                                               ; preds = %3
  store i32 17, ptr %7, align 4, !dbg !1393
  br label %40, !dbg !1394

38:                                               ; preds = %3
  store i32 18, ptr %7, align 4, !dbg !1395
  br label %40, !dbg !1396

39:                                               ; preds = %3
  store i32 19, ptr %7, align 4, !dbg !1397
  br label %40, !dbg !1398

40:                                               ; preds = %34, %35, %3, %39, %38, %37, %36
  %41 = load i32, ptr %7, align 4, !dbg !1399
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %41) #8, !dbg !1400
  unreachable, !dbg !1400
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_implicit_conversion_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1401 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1402, !DIExpression(), !1403)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1404, !DIExpression(), !1405)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1406, !DIExpression(), !1407)
  %7 = load ptr, ptr %4, align 8, !dbg !1408
  %8 = load i64, ptr %5, align 8, !dbg !1409
  %9 = load i64, ptr %6, align 8, !dbg !1410
  call void @_ZN7__ubsanL24handleImplicitConversionEP22ImplicitConversionDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1411
  ret void, !dbg !1412
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_invalid_builtin(ptr noundef %0) #4 !dbg !1413 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1418, !DIExpression(), !1419)
  %3 = load ptr, ptr %2, align 8, !dbg !1420
  call void @_ZN7__ubsanL20handleInvalidBuiltinEP18InvalidBuiltinData(ptr noundef %3), !dbg !1421
  ret void, !dbg !1422
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL20handleInvalidBuiltinEP18InvalidBuiltinData(ptr noundef %0) #4 !dbg !1423 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1424, !DIExpression(), !1425)
    #dbg_declare(ptr %3, !1426, !DIExpression(), !1427)
  store i32 14, ptr %3, align 4, !dbg !1427
  %4 = load i32, ptr %3, align 4, !dbg !1428
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %4) #8, !dbg !1429
  unreachable, !dbg !1429
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_invalid_builtin_abort(ptr noundef %0) #4 !dbg !1430 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1431, !DIExpression(), !1432)
  %3 = load ptr, ptr %2, align 8, !dbg !1433
  call void @_ZN7__ubsanL20handleInvalidBuiltinEP18InvalidBuiltinData(ptr noundef %3), !dbg !1434
  ret void, !dbg !1435
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nonnull_return_v1(ptr noundef %0, ptr noundef %1) #4 !dbg !1436 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1442, !DIExpression(), !1443)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1444, !DIExpression(), !1445)
  %5 = load ptr, ptr %3, align 8, !dbg !1446
  %6 = load ptr, ptr %4, align 8, !dbg !1447
  call void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %5, ptr noundef %6, i1 noundef zeroext true), !dbg !1448
  ret void, !dbg !1449
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %0, ptr noundef %1, i1 noundef zeroext %2) #4 !dbg !1450 {
  %4 = alloca ptr, align 8
  %5 = alloca ptr, align 8
  %6 = alloca i8, align 1
  %7 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1453, !DIExpression(), !1454)
  store ptr %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1455, !DIExpression(), !1456)
  %8 = zext i1 %2 to i8
  store i8 %8, ptr %6, align 1
    #dbg_declare(ptr %6, !1457, !DIExpression(), !1458)
    #dbg_declare(ptr %7, !1459, !DIExpression(), !1460)
  %9 = load i8, ptr %6, align 1, !dbg !1461
  %10 = trunc i8 %9 to i1, !dbg !1461
  %11 = zext i1 %10 to i64, !dbg !1461
  %12 = select i1 %10, i32 30, i32 31, !dbg !1461
  store i32 %12, ptr %7, align 4, !dbg !1460
  %13 = load i32, ptr %7, align 4, !dbg !1462
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %13) #8, !dbg !1463
  unreachable, !dbg !1463
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nonnull_return_v1_abort(ptr noundef %0, ptr noundef %1) #4 !dbg !1464 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1465, !DIExpression(), !1466)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1467, !DIExpression(), !1468)
  %5 = load ptr, ptr %3, align 8, !dbg !1469
  %6 = load ptr, ptr %4, align 8, !dbg !1470
  call void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %5, ptr noundef %6, i1 noundef zeroext true), !dbg !1471
  ret void, !dbg !1472
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nullability_return_v1(ptr noundef %0, ptr noundef %1) #4 !dbg !1473 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1474, !DIExpression(), !1475)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1476, !DIExpression(), !1477)
  %5 = load ptr, ptr %3, align 8, !dbg !1478
  %6 = load ptr, ptr %4, align 8, !dbg !1479
  call void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %5, ptr noundef %6, i1 noundef zeroext false), !dbg !1480
  ret void, !dbg !1481
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nullability_return_v1_abort(ptr noundef %0, ptr noundef %1) #4 !dbg !1482 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1483, !DIExpression(), !1484)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1485, !DIExpression(), !1486)
  %5 = load ptr, ptr %3, align 8, !dbg !1487
  %6 = load ptr, ptr %4, align 8, !dbg !1488
  call void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %5, ptr noundef %6, i1 noundef zeroext false), !dbg !1489
  ret void, !dbg !1490
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nonnull_arg(ptr noundef %0) #4 !dbg !1491 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1496, !DIExpression(), !1497)
  %3 = load ptr, ptr %2, align 8, !dbg !1498
  call void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %3, i1 noundef zeroext true), !dbg !1499
  ret void, !dbg !1500
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %0, i1 noundef zeroext %1) #4 !dbg !1501 {
  %3 = alloca ptr, align 8
  %4 = alloca i8, align 1
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1504, !DIExpression(), !1505)
  %6 = zext i1 %1 to i8
  store i8 %6, ptr %4, align 1
    #dbg_declare(ptr %4, !1506, !DIExpression(), !1507)
    #dbg_declare(ptr %5, !1508, !DIExpression(), !1509)
  %7 = load i8, ptr %4, align 1, !dbg !1510
  %8 = trunc i8 %7 to i1, !dbg !1510
  %9 = zext i1 %8 to i64, !dbg !1510
  %10 = select i1 %8, i32 32, i32 33, !dbg !1510
  store i32 %10, ptr %5, align 4, !dbg !1509
  %11 = load i32, ptr %5, align 4, !dbg !1511
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %11) #8, !dbg !1512
  unreachable, !dbg !1512
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nonnull_arg_abort(ptr noundef %0) #4 !dbg !1513 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1514, !DIExpression(), !1515)
  %3 = load ptr, ptr %2, align 8, !dbg !1516
  call void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %3, i1 noundef zeroext true), !dbg !1517
  ret void, !dbg !1518
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nullability_arg(ptr noundef %0) #4 !dbg !1519 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1520, !DIExpression(), !1521)
  %3 = load ptr, ptr %2, align 8, !dbg !1522
  call void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %3, i1 noundef zeroext false), !dbg !1523
  ret void, !dbg !1524
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nullability_arg_abort(ptr noundef %0) #4 !dbg !1525 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1526, !DIExpression(), !1527)
  %3 = load ptr, ptr %2, align 8, !dbg !1528
  call void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %3, i1 noundef zeroext false), !dbg !1529
  ret void, !dbg !1530
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_pointer_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1531 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1536, !DIExpression(), !1537)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1538, !DIExpression(), !1539)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1540, !DIExpression(), !1541)
  %7 = load ptr, ptr %4, align 8, !dbg !1542
  %8 = load i64, ptr %5, align 8, !dbg !1543
  %9 = load i64, ptr %6, align 8, !dbg !1544
  call void @_ZN7__ubsanL25handlePointerOverflowImplEP19PointerOverflowDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1545
  ret void, !dbg !1546
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL25handlePointerOverflowImplEP19PointerOverflowDatamm(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1547 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  %7 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1548, !DIExpression(), !1549)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1550, !DIExpression(), !1551)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1552, !DIExpression(), !1553)
    #dbg_declare(ptr %7, !1554, !DIExpression(), !1555)
  %8 = load i64, ptr %5, align 8, !dbg !1556
  %9 = icmp eq i64 %8, 0, !dbg !1558
  %10 = load i64, ptr %6, align 8
  %11 = icmp eq i64 %10, 0
  %or.cond = select i1 %9, i1 %11, i1 false, !dbg !1559
  br i1 %or.cond, label %12, label %13, !dbg !1559

12:                                               ; preds = %3
  store i32 3, ptr %7, align 4, !dbg !1560
  br label %26, !dbg !1561

13:                                               ; preds = %3
  %14 = load i64, ptr %5, align 8, !dbg !1562
  %15 = icmp eq i64 %14, 0, !dbg !1564
  %16 = load i64, ptr %6, align 8
  %17 = icmp ne i64 %16, 0
  %or.cond3 = select i1 %15, i1 %17, i1 false, !dbg !1565
  br i1 %or.cond3, label %18, label %19, !dbg !1565

18:                                               ; preds = %13
  store i32 4, ptr %7, align 4, !dbg !1566
  br label %26, !dbg !1567

19:                                               ; preds = %13
  %20 = load i64, ptr %5, align 8, !dbg !1568
  %21 = icmp ne i64 %20, 0, !dbg !1570
  %22 = load i64, ptr %6, align 8
  %23 = icmp eq i64 %22, 0
  %or.cond5 = select i1 %21, i1 %23, i1 false, !dbg !1571
  br i1 %or.cond5, label %24, label %25, !dbg !1571

24:                                               ; preds = %19
  store i32 5, ptr %7, align 4, !dbg !1572
  br label %26, !dbg !1573

25:                                               ; preds = %19
  store i32 6, ptr %7, align 4, !dbg !1574
  br label %26

26:                                               ; preds = %18, %25, %24, %12
  %27 = load i32, ptr %7, align 4, !dbg !1575
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %27) #8, !dbg !1576
  unreachable, !dbg !1576
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_pointer_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1577 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1578, !DIExpression(), !1579)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1580, !DIExpression(), !1581)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1582, !DIExpression(), !1583)
  %7 = load ptr, ptr %4, align 8, !dbg !1584
  %8 = load i64, ptr %5, align 8, !dbg !1585
  %9 = load i64, ptr %6, align 8, !dbg !1586
  call void @_ZN7__ubsanL25handlePointerOverflowImplEP19PointerOverflowDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1587
  ret void, !dbg !1588
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_function_type_mismatch(ptr noundef %0, i64 noundef %1) #4 !dbg !1589 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1594, !DIExpression(), !1595)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1596, !DIExpression(), !1597)
  %5 = load ptr, ptr %3, align 8, !dbg !1598
  %6 = load i64, ptr %4, align 8, !dbg !1599
  call void @_ZN7__ubsanL26handleFunctionTypeMismatchEP24FunctionTypeMismatchDatam(ptr noundef %5, i64 noundef %6), !dbg !1600
  ret void, !dbg !1601
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL26handleFunctionTypeMismatchEP24FunctionTypeMismatchDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1602 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1603, !DIExpression(), !1604)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1605, !DIExpression(), !1606)
    #dbg_declare(ptr %5, !1607, !DIExpression(), !1608)
  store i32 29, ptr %5, align 4, !dbg !1608
  %6 = load i32, ptr %5, align 4, !dbg !1609
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %6) #8, !dbg !1610
  unreachable, !dbg !1610
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_function_type_mismatch_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1611 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1612, !DIExpression(), !1613)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1614, !DIExpression(), !1615)
  %5 = load ptr, ptr %3, align 8, !dbg !1616
  %6 = load i64, ptr %4, align 8, !dbg !1617
  call void @_ZN7__ubsanL26handleFunctionTypeMismatchEP24FunctionTypeMismatchDatam(ptr noundef %5, i64 noundef %6), !dbg !1618
  ret void, !dbg !1619
}

; Function Attrs: noreturn nounwind
declare void @abort() #7

; Function Attrs: noinline nounwind sspstrong uwtable
define void @klee_overshift_check(i64 noundef %0, i64 noundef %1) #0 !dbg !1620 {
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  store i64 %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1624, !DIExpression(), !1625)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1626, !DIExpression(), !1627)
  %5 = load i64, ptr %4, align 8, !dbg !1628
  %6 = load i64, ptr %3, align 8, !dbg !1630
  %7 = icmp uge i64 %5, %6, !dbg !1631
  br i1 %7, label %8, label %9, !dbg !1632

8:                                                ; preds = %2
  call void @klee_report_error(ptr noundef @.str.57, i32 noundef 0, ptr noundef @.str.1.58, ptr noundef @.str.2.59) #8, !dbg !1633
  unreachable, !dbg !1633

9:                                                ; preds = %2
  ret void, !dbg !1635
}

attributes #0 = { noinline nounwind sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }
attributes #2 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }
attributes #3 = { noinline nounwind sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { mustprogress noinline sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }
attributes #5 = { mustprogress noinline noreturn sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }
attributes #6 = { mustprogress noinline nounwind sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }
attributes #7 = { noreturn nounwind }
attributes #8 = { noreturn }

!llvm.dbg.cu = !{!210, !212, !215, !218, !318}
!llvm.ident = !{!321, !321, !321, !321, !321}
!llvm.module.flags = !{!322, !323, !324, !325, !326, !327, !328}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 22, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "spikes/clight-permute/tests/equiv-alive2/rejected-driver.c", directory: "/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo", checksumkind: CSK_MD5, checksum: "dfc6df4ab5eba6c0e8a2f55a84aa3701")
!3 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 112, elements: !5)
!4 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!5 = !{!6}
!6 = !DISubrange(count: 14)
!7 = !DIGlobalVariableExpression(var: !8, expr: !DIExpression())
!8 = distinct !DIGlobalVariable(scope: null, file: !2, line: 37, type: !9, isLocal: true, isDefinition: true)
!9 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 104, elements: !10)
!10 = !{!11}
!11 = !DISubrange(count: 13)
!12 = !DIGlobalVariableExpression(var: !13, expr: !DIExpression())
!13 = distinct !DIGlobalVariable(scope: null, file: !2, line: 37, type: !14, isLocal: true, isDefinition: true)
!14 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 184, elements: !16)
!15 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !4)
!16 = !{!17}
!17 = !DISubrange(count: 23)
!18 = !DIGlobalVariableExpression(var: !19, expr: !DIExpression())
!19 = distinct !DIGlobalVariable(scope: null, file: !2, line: 39, type: !20, isLocal: true, isDefinition: true)
!20 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 216, elements: !21)
!21 = !{!22}
!22 = !DISubrange(count: 27)
!23 = !DIGlobalVariableExpression(var: !24, expr: !DIExpression())
!24 = distinct !DIGlobalVariable(scope: null, file: !2, line: 40, type: !25, isLocal: true, isDefinition: true)
!25 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 248, elements: !26)
!26 = !{!27}
!27 = !DISubrange(count: 31)
!28 = !DIGlobalVariableExpression(var: !29, expr: !DIExpression())
!29 = distinct !DIGlobalVariable(scope: null, file: !2, line: 44, type: !9, isLocal: true, isDefinition: true)
!30 = !DIGlobalVariableExpression(var: !31, expr: !DIExpression())
!31 = distinct !DIGlobalVariable(scope: null, file: !32, line: 11, type: !33, isLocal: true, isDefinition: true)
!32 = !DIFile(filename: "spikes/clight-permute/tests/equiv-alive2/completion.c", directory: "/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo", checksumkind: CSK_MD5, checksum: "2facf546377ff8a05c3e70ac3eabea21")
!33 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 136, elements: !34)
!34 = !{!35}
!35 = !DISubrange(count: 17)
!36 = !DIGlobalVariableExpression(var: !37, expr: !DIExpression())
!37 = distinct !DIGlobalVariable(scope: null, file: !38, line: 222, type: !39, isLocal: true, isDefinition: true)
!38 = !DIFile(filename: "runtime/Sanitizer/ubsan/ubsan_handlers.cpp", directory: "/build/source", checksumkind: CSK_MD5, checksum: "677a186f4db206f7f5c1b77c9630c426")
!39 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 16, elements: !40)
!40 = !{!41}
!41 = !DISubrange(count: 2)
!42 = !DIGlobalVariableExpression(var: !43, expr: !DIExpression())
!43 = distinct !DIGlobalVariable(scope: null, file: !38, line: 224, type: !39, isLocal: true, isDefinition: true)
!44 = !DIGlobalVariableExpression(var: !45, expr: !DIExpression())
!45 = distinct !DIGlobalVariable(scope: null, file: !38, line: 226, type: !39, isLocal: true, isDefinition: true)
!46 = !DIGlobalVariableExpression(var: !47, expr: !DIExpression())
!47 = distinct !DIGlobalVariable(scope: null, file: !38, line: 37, type: !48, isLocal: true, isDefinition: true)
!48 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 456, elements: !49)
!49 = !{!50}
!50 = !DISubrange(count: 57)
!51 = !DIGlobalVariableExpression(var: !52, expr: !DIExpression())
!52 = distinct !DIGlobalVariable(scope: null, file: !53, line: 27, type: !54, isLocal: true, isDefinition: true)
!53 = !DIFile(filename: "runtime/Sanitizer/ubsan/ubsan_checks.inc", directory: "/build/source", checksumkind: CSK_MD5, checksum: "1416f3b20c7f6a18ed9af794062d1096")
!54 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 152, elements: !55)
!55 = !{!56}
!56 = !DISubrange(count: 19)
!57 = !DIGlobalVariableExpression(var: !58, expr: !DIExpression())
!58 = distinct !DIGlobalVariable(scope: null, file: !53, line: 28, type: !59, isLocal: true, isDefinition: true)
!59 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 136, elements: !34)
!60 = !DIGlobalVariableExpression(var: !61, expr: !DIExpression())
!61 = distinct !DIGlobalVariable(scope: null, file: !53, line: 31, type: !62, isLocal: true, isDefinition: true)
!62 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 160, elements: !63)
!63 = !{!64}
!64 = !DISubrange(count: 20)
!65 = !DIGlobalVariableExpression(var: !66, expr: !DIExpression())
!66 = distinct !DIGlobalVariable(scope: null, file: !53, line: 32, type: !67, isLocal: true, isDefinition: true)
!67 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 224, elements: !68)
!68 = !{!69}
!69 = !DISubrange(count: 28)
!70 = !DIGlobalVariableExpression(var: !71, expr: !DIExpression())
!71 = distinct !DIGlobalVariable(scope: null, file: !53, line: 34, type: !72, isLocal: true, isDefinition: true)
!72 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 232, elements: !73)
!73 = !{!74}
!74 = !DISubrange(count: 29)
!75 = !DIGlobalVariableExpression(var: !76, expr: !DIExpression())
!76 = distinct !DIGlobalVariable(scope: null, file: !53, line: 36, type: !59, isLocal: true, isDefinition: true)
!77 = !DIGlobalVariableExpression(var: !78, expr: !DIExpression())
!78 = distinct !DIGlobalVariable(scope: null, file: !53, line: 37, type: !14, isLocal: true, isDefinition: true)
!79 = !DIGlobalVariableExpression(var: !80, expr: !DIExpression())
!80 = distinct !DIGlobalVariable(scope: null, file: !53, line: 38, type: !81, isLocal: true, isDefinition: true)
!81 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 168, elements: !82)
!82 = !{!83}
!83 = !DISubrange(count: 21)
!84 = !DIGlobalVariableExpression(var: !85, expr: !DIExpression())
!85 = distinct !DIGlobalVariable(scope: null, file: !53, line: 39, type: !86, isLocal: true, isDefinition: true)
!86 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 200, elements: !87)
!87 = !{!88}
!88 = !DISubrange(count: 25)
!89 = !DIGlobalVariableExpression(var: !90, expr: !DIExpression())
!90 = distinct !DIGlobalVariable(scope: null, file: !53, line: 40, type: !91, isLocal: true, isDefinition: true)
!91 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 192, elements: !92)
!92 = !{!93}
!93 = !DISubrange(count: 24)
!94 = !DIGlobalVariableExpression(var: !95, expr: !DIExpression())
!95 = distinct !DIGlobalVariable(scope: null, file: !53, line: 42, type: !96, isLocal: true, isDefinition: true)
!96 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 208, elements: !97)
!97 = !{!98}
!98 = !DISubrange(count: 26)
!99 = !DIGlobalVariableExpression(var: !100, expr: !DIExpression())
!100 = distinct !DIGlobalVariable(scope: null, file: !53, line: 44, type: !14, isLocal: true, isDefinition: true)
!101 = !DIGlobalVariableExpression(var: !102, expr: !DIExpression())
!102 = distinct !DIGlobalVariable(scope: null, file: !53, line: 46, type: !81, isLocal: true, isDefinition: true)
!103 = !DIGlobalVariableExpression(var: !104, expr: !DIExpression())
!104 = distinct !DIGlobalVariable(scope: null, file: !53, line: 47, type: !62, isLocal: true, isDefinition: true)
!105 = !DIGlobalVariableExpression(var: !106, expr: !DIExpression())
!106 = distinct !DIGlobalVariable(scope: null, file: !53, line: 48, type: !107, isLocal: true, isDefinition: true)
!107 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 144, elements: !108)
!108 = !{!109}
!109 = !DISubrange(count: 18)
!110 = !DIGlobalVariableExpression(var: !111, expr: !DIExpression())
!111 = distinct !DIGlobalVariable(scope: null, file: !53, line: 49, type: !112, isLocal: true, isDefinition: true)
!112 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 296, elements: !113)
!113 = !{!114}
!114 = !DISubrange(count: 37)
!115 = !DIGlobalVariableExpression(var: !116, expr: !DIExpression())
!116 = distinct !DIGlobalVariable(scope: null, file: !53, line: 52, type: !117, isLocal: true, isDefinition: true)
!117 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 280, elements: !118)
!118 = !{!119}
!119 = !DISubrange(count: 35)
!120 = !DIGlobalVariableExpression(var: !121, expr: !DIExpression())
!121 = distinct !DIGlobalVariable(scope: null, file: !53, line: 55, type: !72, isLocal: true, isDefinition: true)
!122 = !DIGlobalVariableExpression(var: !123, expr: !DIExpression())
!123 = distinct !DIGlobalVariable(scope: null, file: !53, line: 58, type: !124, isLocal: true, isDefinition: true)
!124 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 400, elements: !125)
!125 = !{!126}
!126 = !DISubrange(count: 50)
!127 = !DIGlobalVariableExpression(var: !128, expr: !DIExpression())
!128 = distinct !DIGlobalVariable(scope: null, file: !53, line: 61, type: !54, isLocal: true, isDefinition: true)
!129 = !DIGlobalVariableExpression(var: !130, expr: !DIExpression())
!130 = distinct !DIGlobalVariable(scope: null, file: !53, line: 62, type: !14, isLocal: true, isDefinition: true)
!131 = !DIGlobalVariableExpression(var: !132, expr: !DIExpression())
!132 = distinct !DIGlobalVariable(scope: null, file: !53, line: 63, type: !62, isLocal: true, isDefinition: true)
!133 = !DIGlobalVariableExpression(var: !134, expr: !DIExpression())
!134 = distinct !DIGlobalVariable(scope: null, file: !53, line: 64, type: !59, isLocal: true, isDefinition: true)
!135 = !DIGlobalVariableExpression(var: !136, expr: !DIExpression())
!136 = distinct !DIGlobalVariable(scope: null, file: !53, line: 65, type: !137, isLocal: true, isDefinition: true)
!137 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 120, elements: !138)
!138 = !{!139}
!139 = !DISubrange(count: 15)
!140 = !DIGlobalVariableExpression(var: !141, expr: !DIExpression())
!141 = distinct !DIGlobalVariable(scope: null, file: !53, line: 66, type: !14, isLocal: true, isDefinition: true)
!142 = !DIGlobalVariableExpression(var: !143, expr: !DIExpression())
!143 = distinct !DIGlobalVariable(scope: null, file: !53, line: 67, type: !62, isLocal: true, isDefinition: true)
!144 = !DIGlobalVariableExpression(var: !145, expr: !DIExpression())
!145 = distinct !DIGlobalVariable(scope: null, file: !53, line: 68, type: !107, isLocal: true, isDefinition: true)
!146 = !DIGlobalVariableExpression(var: !147, expr: !DIExpression())
!147 = distinct !DIGlobalVariable(scope: null, file: !53, line: 69, type: !107, isLocal: true, isDefinition: true)
!148 = !DIGlobalVariableExpression(var: !149, expr: !DIExpression())
!149 = distinct !DIGlobalVariable(scope: null, file: !53, line: 70, type: !14, isLocal: true, isDefinition: true)
!150 = !DIGlobalVariableExpression(var: !151, expr: !DIExpression())
!151 = distinct !DIGlobalVariable(scope: null, file: !53, line: 71, type: !62, isLocal: true, isDefinition: true)
!152 = !DIGlobalVariableExpression(var: !153, expr: !DIExpression())
!153 = distinct !DIGlobalVariable(scope: null, file: !53, line: 75, type: !154, isLocal: true, isDefinition: true)
!154 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 176, elements: !155)
!155 = !{!156}
!156 = !DISubrange(count: 22)
!157 = !DIGlobalVariableExpression(var: !158, expr: !DIExpression())
!158 = distinct !DIGlobalVariable(scope: null, file: !53, line: 78, type: !154, isLocal: true, isDefinition: true)
!159 = !DIGlobalVariableExpression(var: !160, expr: !DIExpression())
!160 = distinct !DIGlobalVariable(scope: null, file: !53, line: 79, type: !161, isLocal: true, isDefinition: true)
!161 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 104, elements: !10)
!162 = !DIGlobalVariableExpression(var: !163, expr: !DIExpression())
!163 = distinct !DIGlobalVariable(scope: null, file: !38, line: 46, type: !164, isLocal: true, isDefinition: true)
!164 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 72, elements: !165)
!165 = !{!166}
!166 = !DISubrange(count: 9)
!167 = !DIGlobalVariableExpression(var: !168, expr: !DIExpression())
!168 = distinct !DIGlobalVariable(scope: null, file: !38, line: 55, type: !169, isLocal: true, isDefinition: true)
!169 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 64, elements: !170)
!170 = !{!171}
!171 = !DISubrange(count: 8)
!172 = !DIGlobalVariableExpression(var: !173, expr: !DIExpression())
!173 = distinct !DIGlobalVariable(scope: null, file: !38, line: 62, type: !161, isLocal: true, isDefinition: true)
!174 = !DIGlobalVariableExpression(var: !175, expr: !DIExpression())
!175 = distinct !DIGlobalVariable(scope: null, file: !38, line: 65, type: !169, isLocal: true, isDefinition: true)
!176 = !DIGlobalVariableExpression(var: !177, expr: !DIExpression())
!177 = distinct !DIGlobalVariable(scope: null, file: !38, line: 67, type: !91, isLocal: true, isDefinition: true)
!178 = !DIGlobalVariableExpression(var: !179, expr: !DIExpression())
!179 = distinct !DIGlobalVariable(scope: null, file: !38, line: 74, type: !91, isLocal: true, isDefinition: true)
!180 = !DIGlobalVariableExpression(var: !181, expr: !DIExpression())
!181 = distinct !DIGlobalVariable(scope: null, file: !38, line: 77, type: !91, isLocal: true, isDefinition: true)
!182 = !DIGlobalVariableExpression(var: !183, expr: !DIExpression())
!183 = distinct !DIGlobalVariable(scope: null, file: !38, line: 84, type: !81, isLocal: true, isDefinition: true)
!184 = !DIGlobalVariableExpression(var: !185, expr: !DIExpression())
!185 = distinct !DIGlobalVariable(scope: null, file: !38, line: 86, type: !54, isLocal: true, isDefinition: true)
!186 = !DIGlobalVariableExpression(var: !187, expr: !DIExpression())
!187 = distinct !DIGlobalVariable(scope: null, file: !38, line: 93, type: !59, isLocal: true, isDefinition: true)
!188 = !DIGlobalVariableExpression(var: !189, expr: !DIExpression())
!189 = distinct !DIGlobalVariable(scope: null, file: !38, line: 96, type: !190, isLocal: true, isDefinition: true)
!190 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 216, elements: !21)
!191 = !DIGlobalVariableExpression(var: !192, expr: !DIExpression())
!192 = distinct !DIGlobalVariable(scope: null, file: !38, line: 105, type: !14, isLocal: true, isDefinition: true)
!193 = !DIGlobalVariableExpression(var: !194, expr: !DIExpression())
!194 = distinct !DIGlobalVariable(scope: null, file: !38, line: 250, type: !96, isLocal: true, isDefinition: true)
!195 = !DIGlobalVariableExpression(var: !196, expr: !DIExpression())
!196 = distinct !DIGlobalVariable(scope: null, file: !38, line: 272, type: !62, isLocal: true, isDefinition: true)
!197 = !DIGlobalVariableExpression(var: !198, expr: !DIExpression())
!198 = distinct !DIGlobalVariable(scope: null, file: !38, line: 354, type: !54, isLocal: true, isDefinition: true)
!199 = !DIGlobalVariableExpression(var: !200, expr: !DIExpression())
!200 = distinct !DIGlobalVariable(scope: null, file: !201, line: 27, type: !169, isLocal: true, isDefinition: true)
!201 = !DIFile(filename: "runtime/Intrinsic/klee_overshift_check.c", directory: "/build/source", checksumkind: CSK_MD5, checksum: "5666ed772284910b5d0f856859e4d123")
!202 = !DIGlobalVariableExpression(var: !203, expr: !DIExpression())
!203 = distinct !DIGlobalVariable(scope: null, file: !201, line: 27, type: !204, isLocal: true, isDefinition: true)
!204 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 128, elements: !205)
!205 = !{!206}
!206 = !DISubrange(count: 16)
!207 = !DIGlobalVariableExpression(var: !208, expr: !DIExpression())
!208 = distinct !DIGlobalVariable(scope: null, file: !201, line: 27, type: !209, isLocal: true, isDefinition: true)
!209 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 112, elements: !5)
!210 = distinct !DICompileUnit(language: DW_LANG_C11, file: !211, producer: "clang version 19.1.7", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!211 = !DIFile(filename: "/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo/spikes/clight-permute/permute.c", directory: "/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo", checksumkind: CSK_MD5, checksum: "0369ebff682a97d88e2541b8ad08d62e")
!212 = distinct !DICompileUnit(language: DW_LANG_C11, file: !213, producer: "clang version 19.1.7", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !214, splitDebugInlining: false, nameTableKind: None)
!213 = !DIFile(filename: "/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo/spikes/clight-permute/tests/equiv-alive2/rejected-driver.c", directory: "/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo", checksumkind: CSK_MD5, checksum: "dfc6df4ab5eba6c0e8a2f55a84aa3701")
!214 = !{!0, !7, !12, !18, !23, !28}
!215 = distinct !DICompileUnit(language: DW_LANG_C11, file: !216, producer: "clang version 19.1.7", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !217, splitDebugInlining: false, nameTableKind: None)
!216 = !DIFile(filename: "/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo/spikes/clight-permute/tests/equiv-alive2/completion.c", directory: "/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo", checksumkind: CSK_MD5, checksum: "2facf546377ff8a05c3e70ac3eabea21")
!217 = !{!30}
!218 = distinct !DICompileUnit(language: DW_LANG_C_plus_plus_14, file: !219, producer: "clang version 19.1.7", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !220, retainedTypes: !310, globals: !313, imports: !314, splitDebugInlining: false, nameTableKind: None)
!219 = !DIFile(filename: "/build/source/runtime/Sanitizer/ubsan/ubsan_handlers.cpp", directory: "/build/source/build/runtime/Sanitizer", checksumkind: CSK_MD5, checksum: "677a186f4db206f7f5c1b77c9630c426")
!220 = !{!221, !256, !296}
!221 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "Kind", scope: !223, file: !222, line: 54, baseType: !251, size: 32, elements: !252, identifier: "_ZTSN7__ubsan14TypeDescriptor4KindE")
!222 = !DIFile(filename: "runtime/Sanitizer/ubsan/ubsan_value.h", directory: "/build/source", checksumkind: CSK_MD5, checksum: "420f7cb836bc5a6ee3d0325e2aea7b2e")
!223 = distinct !DICompositeType(tag: DW_TAG_class_type, name: "TypeDescriptor", scope: !224, file: !222, line: 40, size: 48, flags: DIFlagTypePassByValue, elements: !225, identifier: "_ZTSN7__ubsan14TypeDescriptorE")
!224 = !DINamespace(name: "__ubsan", scope: null)
!225 = !{!226, !231, !232, !236, !242, !245, !249, !250}
!226 = !DIDerivedType(tag: DW_TAG_member, name: "TypeKind", scope: !223, file: !222, line: 43, baseType: !227, size: 16)
!227 = !DIDerivedType(tag: DW_TAG_typedef, name: "u16", scope: !229, file: !228, line: 42, baseType: !230)
!228 = !DIFile(filename: "runtime/Sanitizer/ubsan/../sanitizer_common/sanitizer_internal_defs.h", directory: "/build/source", checksumkind: CSK_MD5, checksum: "9855e049a2b86d9a75e59ae446af3488")
!229 = !DINamespace(name: "__sanitizer", scope: null)
!230 = !DIBasicType(name: "unsigned short", size: 16, encoding: DW_ATE_unsigned)
!231 = !DIDerivedType(tag: DW_TAG_member, name: "TypeInfo", scope: !223, file: !222, line: 47, baseType: !227, size: 16, offset: 16)
!232 = !DIDerivedType(tag: DW_TAG_member, name: "TypeName", scope: !223, file: !222, line: 51, baseType: !233, size: 8, offset: 32)
!233 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 8, elements: !234)
!234 = !{!235}
!235 = !DISubrange(count: 1)
!236 = !DISubprogram(name: "getTypeName", linkageName: "_ZNK7__ubsan14TypeDescriptor11getTypeNameEv", scope: !223, file: !222, line: 68, type: !237, scopeLine: 68, flags: DIFlagPublic | DIFlagPrototyped, spFlags: 0)
!237 = !DISubroutineType(types: !238)
!238 = !{!239, !240}
!239 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !15, size: 64)
!240 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !241, size: 64, flags: DIFlagArtificial | DIFlagObjectPointer)
!241 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !223)
!242 = !DISubprogram(name: "getKind", linkageName: "_ZNK7__ubsan14TypeDescriptor7getKindEv", scope: !223, file: !222, line: 70, type: !243, scopeLine: 70, flags: DIFlagPublic | DIFlagPrototyped, spFlags: 0)
!243 = !DISubroutineType(types: !244)
!244 = !{!221, !240}
!245 = !DISubprogram(name: "isIntegerTy", linkageName: "_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv", scope: !223, file: !222, line: 72, type: !246, scopeLine: 72, flags: DIFlagPublic | DIFlagPrototyped, spFlags: 0)
!246 = !DISubroutineType(types: !247)
!247 = !{!248, !240}
!248 = !DIBasicType(name: "bool", size: 8, encoding: DW_ATE_boolean)
!249 = !DISubprogram(name: "isSignedIntegerTy", linkageName: "_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv", scope: !223, file: !222, line: 73, type: !246, scopeLine: 73, flags: DIFlagPublic | DIFlagPrototyped, spFlags: 0)
!250 = !DISubprogram(name: "isUnsignedIntegerTy", linkageName: "_ZNK7__ubsan14TypeDescriptor19isUnsignedIntegerTyEv", scope: !223, file: !222, line: 74, type: !246, scopeLine: 74, flags: DIFlagPublic | DIFlagPrototyped, spFlags: 0)
!251 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!252 = !{!253, !254, !255}
!253 = !DIEnumerator(name: "TK_Integer", value: 0, isUnsigned: true)
!254 = !DIEnumerator(name: "TK_Float", value: 1, isUnsigned: true)
!255 = !DIEnumerator(name: "TK_Unknown", value: 65535, isUnsigned: true)
!256 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "ErrorType", scope: !224, file: !257, line: 34, baseType: !258, size: 32, flags: DIFlagEnumClass, elements: !259, identifier: "_ZTSN7__ubsan9ErrorTypeE")
!257 = !DIFile(filename: "runtime/Sanitizer/ubsan/ubsan_diag.h", directory: "/build/source", checksumkind: CSK_MD5, checksum: "1d0793a8d9236238cbf6a55f3de39572")
!258 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!259 = !{!260, !261, !262, !263, !264, !265, !266, !267, !268, !269, !270, !271, !272, !273, !274, !275, !276, !277, !278, !279, !280, !281, !282, !283, !284, !285, !286, !287, !288, !289, !290, !291, !292, !293, !294, !295}
!260 = !DIEnumerator(name: "GenericUB", value: 0)
!261 = !DIEnumerator(name: "NullPointerUse", value: 1)
!262 = !DIEnumerator(name: "NullPointerUseWithNullability", value: 2)
!263 = !DIEnumerator(name: "NullptrWithOffset", value: 3)
!264 = !DIEnumerator(name: "NullptrWithNonZeroOffset", value: 4)
!265 = !DIEnumerator(name: "NullptrAfterNonZeroOffset", value: 5)
!266 = !DIEnumerator(name: "PointerOverflow", value: 6)
!267 = !DIEnumerator(name: "MisalignedPointerUse", value: 7)
!268 = !DIEnumerator(name: "AlignmentAssumption", value: 8)
!269 = !DIEnumerator(name: "InsufficientObjectSize", value: 9)
!270 = !DIEnumerator(name: "SignedIntegerOverflow", value: 10)
!271 = !DIEnumerator(name: "UnsignedIntegerOverflow", value: 11)
!272 = !DIEnumerator(name: "IntegerDivideByZero", value: 12)
!273 = !DIEnumerator(name: "FloatDivideByZero", value: 13)
!274 = !DIEnumerator(name: "InvalidBuiltin", value: 14)
!275 = !DIEnumerator(name: "InvalidObjCCast", value: 15)
!276 = !DIEnumerator(name: "ImplicitUnsignedIntegerTruncation", value: 16)
!277 = !DIEnumerator(name: "ImplicitSignedIntegerTruncation", value: 17)
!278 = !DIEnumerator(name: "ImplicitIntegerSignChange", value: 18)
!279 = !DIEnumerator(name: "ImplicitSignedIntegerTruncationOrSignChange", value: 19)
!280 = !DIEnumerator(name: "InvalidShiftBase", value: 20)
!281 = !DIEnumerator(name: "InvalidShiftExponent", value: 21)
!282 = !DIEnumerator(name: "OutOfBoundsIndex", value: 22)
!283 = !DIEnumerator(name: "UnreachableCall", value: 23)
!284 = !DIEnumerator(name: "MissingReturn", value: 24)
!285 = !DIEnumerator(name: "NonPositiveVLAIndex", value: 25)
!286 = !DIEnumerator(name: "FloatCastOverflow", value: 26)
!287 = !DIEnumerator(name: "InvalidBoolLoad", value: 27)
!288 = !DIEnumerator(name: "InvalidEnumLoad", value: 28)
!289 = !DIEnumerator(name: "FunctionTypeMismatch", value: 29)
!290 = !DIEnumerator(name: "InvalidNullReturn", value: 30)
!291 = !DIEnumerator(name: "InvalidNullReturnWithNullability", value: 31)
!292 = !DIEnumerator(name: "InvalidNullArgument", value: 32)
!293 = !DIEnumerator(name: "InvalidNullArgumentWithNullability", value: 33)
!294 = !DIEnumerator(name: "DynamicTypeMismatch", value: 34)
!295 = !DIEnumerator(name: "CFIBadType", value: 35)
!296 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "TypeCheckKind", scope: !224, file: !38, line: 122, baseType: !251, size: 32, elements: !297, identifier: "_ZTSN7__ubsan13TypeCheckKindE")
!297 = !{!298, !299, !300, !301, !302, !303, !304, !305, !306, !307, !308, !309}
!298 = !DIEnumerator(name: "TCK_Load", value: 0, isUnsigned: true)
!299 = !DIEnumerator(name: "TCK_Store", value: 1, isUnsigned: true)
!300 = !DIEnumerator(name: "TCK_ReferenceBinding", value: 2, isUnsigned: true)
!301 = !DIEnumerator(name: "TCK_MemberAccess", value: 3, isUnsigned: true)
!302 = !DIEnumerator(name: "TCK_MemberCall", value: 4, isUnsigned: true)
!303 = !DIEnumerator(name: "TCK_ConstructorCall", value: 5, isUnsigned: true)
!304 = !DIEnumerator(name: "TCK_DowncastPointer", value: 6, isUnsigned: true)
!305 = !DIEnumerator(name: "TCK_DowncastReference", value: 7, isUnsigned: true)
!306 = !DIEnumerator(name: "TCK_Upcast", value: 8, isUnsigned: true)
!307 = !DIEnumerator(name: "TCK_UpcastToVirtualBase", value: 9, isUnsigned: true)
!308 = !DIEnumerator(name: "TCK_NonnullAssign", value: 10, isUnsigned: true)
!309 = !DIEnumerator(name: "TCK_DynamicOperation", value: 11, isUnsigned: true)
!310 = !{!311, !221}
!311 = !DIDerivedType(tag: DW_TAG_typedef, name: "uptr", scope: !229, file: !228, line: 33, baseType: !312)
!312 = !DIBasicType(name: "unsigned long", size: 64, encoding: DW_ATE_unsigned)
!313 = !{!36, !42, !44, !46, !51, !57, !60, !65, !70, !75, !77, !79, !84, !89, !94, !99, !101, !103, !105, !110, !115, !120, !122, !127, !129, !131, !133, !135, !140, !142, !144, !146, !148, !150, !152, !157, !159, !162, !167, !172, !174, !176, !178, !180, !182, !184, !186, !188, !191, !193, !195, !197}
!314 = !{!315, !316}
!315 = !DIImportedEntity(tag: DW_TAG_imported_module, scope: !224, entity: !229, file: !228, line: 53)
!316 = !DIImportedEntity(tag: DW_TAG_imported_module, scope: !218, entity: !224, file: !317, line: 23)
!317 = !DIFile(filename: "runtime/Sanitizer/ubsan/ubsan_handlers.h", directory: "/build/source", checksumkind: CSK_MD5, checksum: "5d402a8bb47262beee2be158665f6d54")
!318 = distinct !DICompileUnit(language: DW_LANG_C89, file: !319, producer: "clang version 19.1.7", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !320, splitDebugInlining: false, nameTableKind: None)
!319 = !DIFile(filename: "/build/source/runtime/Intrinsic/klee_overshift_check.c", directory: "/build/source/build/runtime/Intrinsic", checksumkind: CSK_MD5, checksum: "5666ed772284910b5d0f856859e4d123")
!320 = !{!199, !202, !207}
!321 = !{!"clang version 19.1.7"}
!322 = !{i32 7, !"Dwarf Version", i32 5}
!323 = !{i32 2, !"Debug Info Version", i32 3}
!324 = !{i32 1, !"wchar_size", i32 4}
!325 = !{i32 4, !"probe-stack", !"inline-asm"}
!326 = !{i32 8, !"PIC Level", i32 2}
!327 = !{i32 7, !"uwtable", i32 2}
!328 = !{i32 7, !"frame-pointer", i32 2}
!329 = distinct !DISubprogram(name: "permute", scope: !330, file: !330, line: 12, type: !331, scopeLine: 13, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !210, retainedNodes: !334)
!330 = !DIFile(filename: "spikes/clight-permute/permute.c", directory: "/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo", checksumkind: CSK_MD5, checksum: "0369ebff682a97d88e2541b8ad08d62e")
!331 = !DISubroutineType(types: !332)
!332 = !{!251, !251, !333, !333, !333, !333, !333, !333}
!333 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !251, size: 64)
!334 = !{}
!335 = !DILocalVariable(name: "v1", arg: 1, scope: !329, file: !330, line: 12, type: !251)
!336 = !DILocation(line: 12, column: 35, scope: !329)
!337 = !DILocalVariable(name: "v2", arg: 2, scope: !329, file: !330, line: 12, type: !333)
!338 = !DILocation(line: 12, column: 53, scope: !329)
!339 = !DILocalVariable(name: "v3", arg: 3, scope: !329, file: !330, line: 12, type: !333)
!340 = !DILocation(line: 12, column: 71, scope: !329)
!341 = !DILocalVariable(name: "v4", arg: 4, scope: !329, file: !330, line: 12, type: !333)
!342 = !DILocation(line: 12, column: 89, scope: !329)
!343 = !DILocalVariable(name: "v5", arg: 5, scope: !329, file: !330, line: 12, type: !333)
!344 = !DILocation(line: 12, column: 107, scope: !329)
!345 = !DILocalVariable(name: "v6", arg: 6, scope: !329, file: !330, line: 12, type: !333)
!346 = !DILocation(line: 12, column: 125, scope: !329)
!347 = !DILocalVariable(name: "v7", arg: 7, scope: !329, file: !330, line: 12, type: !333)
!348 = !DILocation(line: 12, column: 143, scope: !329)
!349 = !DILocalVariable(name: "v8", scope: !329, file: !330, line: 14, type: !251)
!350 = !DILocation(line: 14, column: 16, scope: !329)
!351 = !DILocalVariable(name: "v9", scope: !329, file: !330, line: 15, type: !251)
!352 = !DILocation(line: 15, column: 16, scope: !329)
!353 = !DILocalVariable(name: "v10", scope: !329, file: !330, line: 16, type: !251)
!354 = !DILocation(line: 16, column: 16, scope: !329)
!355 = !DILocalVariable(name: "v11", scope: !329, file: !330, line: 17, type: !251)
!356 = !DILocation(line: 17, column: 16, scope: !329)
!357 = !DILocalVariable(name: "v12", scope: !329, file: !330, line: 18, type: !251)
!358 = !DILocation(line: 18, column: 16, scope: !329)
!359 = !DILocalVariable(name: "v13", scope: !329, file: !330, line: 19, type: !251)
!360 = !DILocation(line: 19, column: 16, scope: !329)
!361 = !DILocation(line: 20, column: 3, scope: !329)
!362 = !DILocation(line: 20, column: 10, scope: !329)
!363 = !DILocation(line: 21, column: 3, scope: !329)
!364 = !DILocation(line: 21, column: 10, scope: !329)
!365 = !DILocation(line: 22, column: 3, scope: !329)
!366 = !DILocation(line: 22, column: 10, scope: !329)
!367 = !DILocation(line: 23, column: 7, scope: !368)
!368 = distinct !DILexicalBlock(scope: !329, file: !330, line: 23, column: 7)
!369 = !DILocation(line: 23, column: 10, scope: !368)
!370 = !DILocation(line: 23, column: 7, scope: !329)
!371 = !DILocation(line: 24, column: 5, scope: !372)
!372 = distinct !DILexicalBlock(scope: !368, file: !330, line: 23, column: 19)
!373 = !DILocation(line: 27, column: 7, scope: !374)
!374 = distinct !DILexicalBlock(scope: !329, file: !330, line: 27, column: 7)
!375 = !DILocation(line: 27, column: 10, scope: !374)
!376 = !DILocation(line: 27, column: 7, scope: !329)
!377 = !DILocation(line: 28, column: 5, scope: !378)
!378 = distinct !DILexicalBlock(scope: !374, file: !330, line: 27, column: 17)
!379 = !DILocation(line: 31, column: 6, scope: !329)
!380 = !DILocation(line: 32, column: 3, scope: !329)
!381 = !DILocation(line: 33, column: 9, scope: !382)
!382 = distinct !DILexicalBlock(scope: !383, file: !330, line: 33, column: 9)
!383 = distinct !DILexicalBlock(scope: !329, file: !330, line: 32, column: 13)
!384 = !DILocation(line: 33, column: 14, scope: !382)
!385 = !DILocation(line: 33, column: 12, scope: !382)
!386 = !DILocation(line: 33, column: 9, scope: !383)
!387 = !DILocation(line: 37, column: 5, scope: !383)
!388 = !DILocation(line: 37, column: 8, scope: !383)
!389 = !DILocation(line: 37, column: 12, scope: !383)
!390 = !DILocation(line: 38, column: 11, scope: !383)
!391 = !DILocation(line: 38, column: 14, scope: !383)
!392 = !DILocation(line: 38, column: 8, scope: !383)
!393 = distinct !{!393, !380, !394}
!394 = !DILocation(line: 39, column: 3, scope: !329)
!395 = !DILocation(line: 40, column: 6, scope: !329)
!396 = !DILocation(line: 41, column: 3, scope: !329)
!397 = !DILocation(line: 42, column: 9, scope: !398)
!398 = distinct !DILexicalBlock(scope: !399, file: !330, line: 42, column: 9)
!399 = distinct !DILexicalBlock(scope: !329, file: !330, line: 41, column: 13)
!400 = !DILocation(line: 42, column: 14, scope: !398)
!401 = !DILocation(line: 42, column: 12, scope: !398)
!402 = !DILocation(line: 42, column: 9, scope: !399)
!403 = !DILocation(line: 46, column: 10, scope: !399)
!404 = !DILocation(line: 46, column: 13, scope: !399)
!405 = !DILocation(line: 46, column: 8, scope: !399)
!406 = !DILocation(line: 47, column: 9, scope: !407)
!407 = distinct !DILexicalBlock(scope: !399, file: !330, line: 47, column: 9)
!408 = !DILocation(line: 47, column: 15, scope: !407)
!409 = !DILocation(line: 47, column: 12, scope: !407)
!410 = !DILocation(line: 47, column: 9, scope: !399)
!411 = !DILocation(line: 48, column: 7, scope: !412)
!412 = distinct !DILexicalBlock(scope: !407, file: !330, line: 47, column: 19)
!413 = !DILocation(line: 51, column: 9, scope: !414)
!414 = distinct !DILexicalBlock(scope: !399, file: !330, line: 51, column: 9)
!415 = !DILocation(line: 51, column: 12, scope: !414)
!416 = !DILocation(line: 51, column: 16, scope: !414)
!417 = !DILocation(line: 51, column: 9, scope: !399)
!418 = !DILocation(line: 52, column: 7, scope: !419)
!419 = distinct !DILexicalBlock(scope: !414, file: !330, line: 51, column: 23)
!420 = !DILocation(line: 55, column: 5, scope: !399)
!421 = !DILocation(line: 55, column: 8, scope: !399)
!422 = !DILocation(line: 55, column: 12, scope: !399)
!423 = !DILocation(line: 56, column: 14, scope: !399)
!424 = !DILocation(line: 56, column: 17, scope: !399)
!425 = !DILocation(line: 56, column: 5, scope: !399)
!426 = !DILocation(line: 56, column: 8, scope: !399)
!427 = !DILocation(line: 56, column: 12, scope: !399)
!428 = !DILocation(line: 57, column: 11, scope: !399)
!429 = !DILocation(line: 57, column: 14, scope: !399)
!430 = !DILocation(line: 57, column: 8, scope: !399)
!431 = distinct !{!431, !396, !432}
!432 = !DILocation(line: 58, column: 3, scope: !329)
!433 = !DILocation(line: 59, column: 6, scope: !329)
!434 = !DILocation(line: 60, column: 3, scope: !329)
!435 = !DILocation(line: 61, column: 9, scope: !436)
!436 = distinct !DILexicalBlock(scope: !437, file: !330, line: 61, column: 9)
!437 = distinct !DILexicalBlock(scope: !329, file: !330, line: 60, column: 13)
!438 = !DILocation(line: 61, column: 14, scope: !436)
!439 = !DILocation(line: 61, column: 12, scope: !436)
!440 = !DILocation(line: 61, column: 9, scope: !437)
!441 = !DILocation(line: 65, column: 9, scope: !442)
!442 = distinct !DILexicalBlock(scope: !437, file: !330, line: 65, column: 9)
!443 = !DILocation(line: 65, column: 12, scope: !442)
!444 = !DILocation(line: 65, column: 19, scope: !442)
!445 = !DILocation(line: 65, column: 22, scope: !442)
!446 = !DILocation(line: 65, column: 16, scope: !442)
!447 = !DILocation(line: 65, column: 9, scope: !437)
!448 = !DILocation(line: 66, column: 16, scope: !449)
!449 = distinct !DILexicalBlock(scope: !442, file: !330, line: 65, column: 27)
!450 = !DILocation(line: 66, column: 7, scope: !449)
!451 = !DILocation(line: 66, column: 10, scope: !449)
!452 = !DILocation(line: 66, column: 14, scope: !449)
!453 = !DILocation(line: 67, column: 7, scope: !449)
!454 = !DILocation(line: 67, column: 10, scope: !449)
!455 = !DILocation(line: 67, column: 14, scope: !449)
!456 = !DILocation(line: 68, column: 5, scope: !449)
!457 = !DILocation(line: 69, column: 7, scope: !458)
!458 = distinct !DILexicalBlock(scope: !442, file: !330, line: 68, column: 12)
!459 = !DILocation(line: 69, column: 10, scope: !458)
!460 = !DILocation(line: 69, column: 14, scope: !458)
!461 = !DILocation(line: 71, column: 11, scope: !437)
!462 = !DILocation(line: 71, column: 14, scope: !437)
!463 = !DILocation(line: 71, column: 8, scope: !437)
!464 = distinct !{!464, !434, !465}
!465 = !DILocation(line: 72, column: 3, scope: !329)
!466 = !DILocation(line: 73, column: 6, scope: !329)
!467 = !DILocation(line: 74, column: 3, scope: !329)
!468 = !DILocation(line: 75, column: 9, scope: !469)
!469 = distinct !DILexicalBlock(scope: !470, file: !330, line: 75, column: 9)
!470 = distinct !DILexicalBlock(scope: !329, file: !330, line: 74, column: 13)
!471 = !DILocation(line: 75, column: 14, scope: !469)
!472 = !DILocation(line: 75, column: 12, scope: !469)
!473 = !DILocation(line: 75, column: 9, scope: !470)
!474 = !DILocation(line: 79, column: 9, scope: !475)
!475 = distinct !DILexicalBlock(scope: !470, file: !330, line: 79, column: 9)
!476 = !DILocation(line: 79, column: 12, scope: !475)
!477 = !DILocation(line: 79, column: 19, scope: !475)
!478 = !DILocation(line: 79, column: 22, scope: !475)
!479 = !DILocation(line: 79, column: 16, scope: !475)
!480 = !DILocation(line: 79, column: 9, scope: !470)
!481 = !DILocation(line: 80, column: 10, scope: !482)
!482 = distinct !DILexicalBlock(scope: !475, file: !330, line: 79, column: 27)
!483 = !DILocation(line: 81, column: 7, scope: !482)
!484 = !DILocation(line: 82, column: 13, scope: !485)
!485 = distinct !DILexicalBlock(scope: !486, file: !330, line: 82, column: 13)
!486 = distinct !DILexicalBlock(scope: !482, file: !330, line: 81, column: 17)
!487 = !DILocation(line: 82, column: 18, scope: !485)
!488 = !DILocation(line: 82, column: 16, scope: !485)
!489 = !DILocation(line: 82, column: 13, scope: !486)
!490 = !DILocation(line: 86, column: 13, scope: !491)
!491 = distinct !DILexicalBlock(scope: !486, file: !330, line: 86, column: 13)
!492 = !DILocation(line: 86, column: 16, scope: !491)
!493 = !DILocation(line: 86, column: 20, scope: !491)
!494 = !DILocation(line: 86, column: 13, scope: !486)
!495 = !DILocation(line: 87, column: 15, scope: !496)
!496 = distinct !DILexicalBlock(scope: !497, file: !330, line: 87, column: 15)
!497 = distinct !DILexicalBlock(scope: !491, file: !330, line: 86, column: 27)
!498 = !DILocation(line: 87, column: 18, scope: !496)
!499 = !DILocation(line: 87, column: 25, scope: !496)
!500 = !DILocation(line: 87, column: 28, scope: !496)
!501 = !DILocation(line: 87, column: 22, scope: !496)
!502 = !DILocation(line: 87, column: 15, scope: !497)
!503 = !DILocation(line: 93, column: 15, scope: !486)
!504 = !DILocation(line: 93, column: 18, scope: !486)
!505 = !DILocation(line: 93, column: 12, scope: !486)
!506 = distinct !{!506, !483, !507}
!507 = !DILocation(line: 94, column: 7, scope: !482)
!508 = !DILocation(line: 95, column: 11, scope: !509)
!509 = distinct !DILexicalBlock(scope: !482, file: !330, line: 95, column: 11)
!510 = !DILocation(line: 95, column: 17, scope: !509)
!511 = !DILocation(line: 95, column: 14, scope: !509)
!512 = !DILocation(line: 95, column: 11, scope: !482)
!513 = !DILocation(line: 96, column: 9, scope: !514)
!514 = distinct !DILexicalBlock(scope: !509, file: !330, line: 95, column: 21)
!515 = !DILocation(line: 99, column: 16, scope: !482)
!516 = !DILocation(line: 99, column: 7, scope: !482)
!517 = !DILocation(line: 99, column: 10, scope: !482)
!518 = !DILocation(line: 99, column: 14, scope: !482)
!519 = !DILocation(line: 100, column: 7, scope: !482)
!520 = !DILocation(line: 100, column: 10, scope: !482)
!521 = !DILocation(line: 100, column: 14, scope: !482)
!522 = !DILocation(line: 101, column: 5, scope: !482)
!523 = !DILocation(line: 103, column: 11, scope: !470)
!524 = !DILocation(line: 103, column: 14, scope: !470)
!525 = !DILocation(line: 103, column: 8, scope: !470)
!526 = distinct !{!526, !467, !527}
!527 = !DILocation(line: 104, column: 3, scope: !329)
!528 = !DILocation(line: 105, column: 10, scope: !329)
!529 = !DILocation(line: 105, column: 13, scope: !329)
!530 = !DILocation(line: 105, column: 7, scope: !329)
!531 = !DILocation(line: 106, column: 3, scope: !329)
!532 = !DILocation(line: 107, column: 11, scope: !533)
!533 = distinct !DILexicalBlock(scope: !329, file: !330, line: 106, column: 13)
!534 = !DILocation(line: 107, column: 14, scope: !533)
!535 = !DILocation(line: 107, column: 9, scope: !533)
!536 = !DILocation(line: 108, column: 9, scope: !537)
!537 = distinct !DILexicalBlock(scope: !533, file: !330, line: 108, column: 9)
!538 = !DILocation(line: 108, column: 16, scope: !537)
!539 = !DILocation(line: 108, column: 13, scope: !537)
!540 = !DILocation(line: 108, column: 9, scope: !533)
!541 = !DILocation(line: 110, column: 13, scope: !542)
!542 = distinct !DILexicalBlock(scope: !543, file: !330, line: 110, column: 13)
!543 = distinct !DILexicalBlock(scope: !544, file: !330, line: 109, column: 17)
!544 = distinct !DILexicalBlock(scope: !537, file: !330, line: 108, column: 21)
!545 = !DILocation(line: 110, column: 17, scope: !542)
!546 = !DILocation(line: 110, column: 13, scope: !543)
!547 = !DILocation(line: 114, column: 16, scope: !543)
!548 = !DILocation(line: 114, column: 20, scope: !543)
!549 = !DILocation(line: 114, column: 13, scope: !543)
!550 = !DILocation(line: 115, column: 13, scope: !551)
!551 = distinct !DILexicalBlock(scope: !543, file: !330, line: 115, column: 13)
!552 = !DILocation(line: 115, column: 16, scope: !551)
!553 = !DILocation(line: 115, column: 24, scope: !551)
!554 = !DILocation(line: 115, column: 21, scope: !551)
!555 = !DILocation(line: 115, column: 13, scope: !543)
!556 = distinct !{!556, !557, !558}
!557 = !DILocation(line: 109, column: 7, scope: !544)
!558 = !DILocation(line: 119, column: 7, scope: !544)
!559 = !DILocation(line: 120, column: 11, scope: !560)
!560 = distinct !DILexicalBlock(scope: !544, file: !330, line: 120, column: 11)
!561 = !DILocation(line: 120, column: 14, scope: !560)
!562 = !DILocation(line: 120, column: 22, scope: !560)
!563 = !DILocation(line: 120, column: 19, scope: !560)
!564 = !DILocation(line: 120, column: 11, scope: !544)
!565 = !DILocation(line: 121, column: 9, scope: !566)
!566 = distinct !DILexicalBlock(scope: !560, file: !330, line: 120, column: 27)
!567 = !DILocation(line: 126, column: 9, scope: !568)
!568 = distinct !DILexicalBlock(scope: !533, file: !330, line: 126, column: 9)
!569 = !DILocation(line: 126, column: 12, scope: !568)
!570 = !DILocation(line: 126, column: 20, scope: !568)
!571 = !DILocation(line: 126, column: 23, scope: !568)
!572 = !DILocation(line: 126, column: 17, scope: !568)
!573 = !DILocation(line: 126, column: 9, scope: !533)
!574 = !DILocation(line: 127, column: 14, scope: !575)
!575 = distinct !DILexicalBlock(scope: !568, file: !330, line: 126, column: 29)
!576 = !DILocation(line: 127, column: 20, scope: !575)
!577 = !DILocation(line: 127, column: 18, scope: !575)
!578 = !DILocation(line: 127, column: 11, scope: !575)
!579 = !DILocation(line: 128, column: 11, scope: !580)
!580 = distinct !DILexicalBlock(scope: !575, file: !330, line: 128, column: 11)
!581 = !DILocation(line: 128, column: 15, scope: !580)
!582 = !DILocation(line: 128, column: 11, scope: !575)
!583 = !DILocation(line: 129, column: 18, scope: !584)
!584 = distinct !DILexicalBlock(scope: !580, file: !330, line: 128, column: 22)
!585 = !DILocation(line: 129, column: 9, scope: !584)
!586 = !DILocation(line: 129, column: 16, scope: !584)
!587 = !DILocation(line: 130, column: 19, scope: !584)
!588 = !DILocation(line: 130, column: 23, scope: !584)
!589 = !DILocation(line: 130, column: 9, scope: !584)
!590 = !DILocation(line: 130, column: 16, scope: !584)
!591 = !DILocation(line: 131, column: 9, scope: !584)
!592 = !DILocation(line: 134, column: 11, scope: !593)
!593 = distinct !DILexicalBlock(scope: !575, file: !330, line: 134, column: 11)
!594 = !DILocation(line: 134, column: 22, scope: !593)
!595 = !DILocation(line: 134, column: 27, scope: !593)
!596 = !DILocation(line: 134, column: 25, scope: !593)
!597 = !DILocation(line: 134, column: 18, scope: !593)
!598 = !DILocation(line: 134, column: 11, scope: !575)
!599 = !DILocation(line: 135, column: 9, scope: !600)
!600 = distinct !DILexicalBlock(scope: !593, file: !330, line: 134, column: 32)
!601 = !DILocation(line: 138, column: 13, scope: !575)
!602 = !DILocation(line: 138, column: 16, scope: !575)
!603 = !DILocation(line: 138, column: 11, scope: !575)
!604 = !DILocation(line: 139, column: 17, scope: !575)
!605 = !DILocation(line: 139, column: 20, scope: !575)
!606 = !DILocation(line: 139, column: 7, scope: !575)
!607 = !DILocation(line: 139, column: 10, scope: !575)
!608 = !DILocation(line: 139, column: 15, scope: !575)
!609 = !DILocation(line: 140, column: 17, scope: !575)
!610 = !DILocation(line: 140, column: 7, scope: !575)
!611 = !DILocation(line: 140, column: 10, scope: !575)
!612 = !DILocation(line: 140, column: 15, scope: !575)
!613 = !DILocation(line: 141, column: 20, scope: !575)
!614 = !DILocation(line: 141, column: 7, scope: !575)
!615 = !DILocation(line: 141, column: 10, scope: !575)
!616 = !DILocation(line: 141, column: 18, scope: !575)
!617 = !DILocation(line: 142, column: 17, scope: !575)
!618 = !DILocation(line: 142, column: 24, scope: !575)
!619 = !DILocation(line: 142, column: 7, scope: !575)
!620 = !DILocation(line: 142, column: 14, scope: !575)
!621 = !DILocation(line: 143, column: 5, scope: !575)
!622 = !DILocation(line: 145, column: 11, scope: !533)
!623 = !DILocation(line: 145, column: 14, scope: !533)
!624 = !DILocation(line: 145, column: 9, scope: !533)
!625 = !DILocation(line: 146, column: 15, scope: !533)
!626 = !DILocation(line: 146, column: 18, scope: !533)
!627 = !DILocation(line: 146, column: 5, scope: !533)
!628 = !DILocation(line: 146, column: 8, scope: !533)
!629 = !DILocation(line: 146, column: 13, scope: !533)
!630 = !DILocation(line: 147, column: 15, scope: !533)
!631 = !DILocation(line: 147, column: 5, scope: !533)
!632 = !DILocation(line: 147, column: 8, scope: !533)
!633 = !DILocation(line: 147, column: 13, scope: !533)
!634 = distinct !{!634, !531, !635}
!635 = !DILocation(line: 148, column: 3, scope: !329)
!636 = !DILocation(line: 149, column: 1, scope: !329)
!637 = distinct !DISubprogram(name: "checked_main", scope: !2, file: !2, line: 7, type: !638, scopeLine: 8, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !212, retainedNodes: !334)
!638 = !DISubroutineType(types: !639)
!639 = !{!258}
!640 = !DILocalVariable(name: "input", scope: !637, file: !2, line: 19, type: !641)
!641 = !DICompositeType(tag: DW_TAG_array_type, baseType: !251, size: 1248, elements: !642)
!642 = !{!643}
!643 = !DISubrange(count: 39)
!644 = !DILocation(line: 19, column: 14, scope: !637)
!645 = !DILocalVariable(name: "data", scope: !637, file: !2, line: 20, type: !646)
!646 = !DICompositeType(tag: DW_TAG_array_type, baseType: !251, size: 576, elements: !108)
!647 = !DILocation(line: 20, column: 14, scope: !637)
!648 = !DILocalVariable(name: "permutation", scope: !637, file: !2, line: 20, type: !646)
!649 = !DILocation(line: 20, column: 30, scope: !637)
!650 = !DILocalVariable(name: "target", scope: !637, file: !2, line: 21, type: !646)
!651 = !DILocation(line: 21, column: 14, scope: !637)
!652 = !DILocalVariable(name: "used", scope: !637, file: !2, line: 21, type: !646)
!653 = !DILocation(line: 21, column: 32, scope: !637)
!654 = !DILocalVariable(name: "trace", scope: !637, file: !2, line: 21, type: !655)
!655 = !DICompositeType(tag: DW_TAG_array_type, baseType: !251, size: 1152, elements: !656)
!656 = !{!657}
!657 = !DISubrange(count: 36)
!658 = !DILocation(line: 21, column: 48, scope: !637)
!659 = !DILocalVariable(name: "out", scope: !637, file: !2, line: 21, type: !660)
!660 = !DICompositeType(tag: DW_TAG_array_type, baseType: !251, size: 96, elements: !661)
!661 = !{!662}
!662 = !DISubrange(count: 3)
!663 = !DILocation(line: 21, column: 70, scope: !637)
!664 = !DILocation(line: 22, column: 24, scope: !637)
!665 = !DILocation(line: 22, column: 5, scope: !637)
!666 = !DILocalVariable(name: "valid", scope: !637, file: !2, line: 23, type: !251)
!667 = !DILocation(line: 23, column: 14, scope: !637)
!668 = !DILocalVariable(name: "i", scope: !669, file: !2, line: 24, type: !251)
!669 = distinct !DILexicalBlock(scope: !637, file: !2, line: 24, column: 5)
!670 = !DILocation(line: 24, column: 19, scope: !669)
!671 = !DILocation(line: 24, column: 10, scope: !669)
!672 = !DILocation(line: 24, column: 26, scope: !673)
!673 = distinct !DILexicalBlock(scope: !669, file: !2, line: 24, column: 5)
!674 = !DILocation(line: 24, column: 28, scope: !673)
!675 = !DILocation(line: 24, column: 5, scope: !669)
!676 = !DILocation(line: 25, column: 24, scope: !677)
!677 = distinct !DILexicalBlock(scope: !673, file: !2, line: 24, column: 45)
!678 = !DILocation(line: 25, column: 18, scope: !677)
!679 = !{!"branch_weights", i32 1048575, i32 1}
!680 = !DILocation(line: 25, column: 27, scope: !677)
!681 = !DILocation(line: 25, column: 15, scope: !677)
!682 = !DILocalVariable(name: "j", scope: !683, file: !2, line: 26, type: !251)
!683 = distinct !DILexicalBlock(scope: !677, file: !2, line: 26, column: 9)
!684 = !DILocation(line: 26, column: 23, scope: !683)
!685 = !DILocation(line: 26, column: 14, scope: !683)
!686 = !DILocation(line: 26, column: 30, scope: !687)
!687 = distinct !DILexicalBlock(scope: !683, file: !2, line: 26, column: 9)
!688 = !DILocation(line: 26, column: 34, scope: !687)
!689 = !DILocation(line: 26, column: 32, scope: !687)
!690 = !DILocation(line: 26, column: 9, scope: !683)
!691 = !DILocation(line: 27, column: 28, scope: !687)
!692 = !DILocation(line: 27, column: 22, scope: !687)
!693 = !DILocation(line: 27, column: 40, scope: !687)
!694 = !DILocation(line: 27, column: 34, scope: !687)
!695 = !DILocation(line: 27, column: 31, scope: !687)
!696 = !DILocation(line: 27, column: 19, scope: !687)
!697 = !DILocation(line: 26, column: 37, scope: !687)
!698 = !DILocation(line: 26, column: 9, scope: !687)
!699 = distinct !{!699, !690, !700, !701}
!700 = !DILocation(line: 27, column: 41, scope: !683)
!701 = !{!"llvm.loop.mustprogress"}
!702 = !DILocation(line: 28, column: 32, scope: !677)
!703 = !DILocation(line: 28, column: 26, scope: !677)
!704 = !DILocation(line: 28, column: 21, scope: !677)
!705 = !DILocation(line: 28, column: 24, scope: !677)
!706 = !DILocation(line: 29, column: 36, scope: !677)
!707 = !DILocation(line: 29, column: 34, scope: !677)
!708 = !DILocation(line: 29, column: 19, scope: !677)
!709 = !DILocation(line: 29, column: 14, scope: !677)
!710 = !DILocation(line: 29, column: 17, scope: !677)
!711 = !DILocation(line: 24, column: 40, scope: !673)
!712 = !DILocation(line: 24, column: 5, scope: !673)
!713 = distinct !{!713, !675, !714, !701}
!714 = !DILocation(line: 30, column: 5, scope: !669)
!715 = !DILocation(line: 33, column: 17, scope: !637)
!716 = !DILocation(line: 33, column: 23, scope: !637)
!717 = !DILocation(line: 33, column: 5, scope: !637)
!718 = !DILocalVariable(name: "i", scope: !719, file: !2, line: 34, type: !251)
!719 = distinct !DILexicalBlock(scope: !637, file: !2, line: 34, column: 5)
!720 = !DILocation(line: 34, column: 19, scope: !719)
!721 = !DILocation(line: 34, column: 10, scope: !719)
!722 = !DILocation(line: 34, column: 26, scope: !723)
!723 = distinct !DILexicalBlock(scope: !719, file: !2, line: 34, column: 5)
!724 = !DILocation(line: 34, column: 28, scope: !723)
!725 = !DILocation(line: 34, column: 5, scope: !719)
!726 = !DILocation(line: 35, column: 40, scope: !723)
!727 = !DILocation(line: 35, column: 38, scope: !723)
!728 = !DILocation(line: 35, column: 18, scope: !723)
!729 = !DILocation(line: 35, column: 13, scope: !723)
!730 = !DILocation(line: 35, column: 16, scope: !723)
!731 = !DILocation(line: 34, column: 34, scope: !723)
!732 = !DILocation(line: 34, column: 5, scope: !723)
!733 = distinct !{!733, !725, !734, !701}
!734 = !DILocation(line: 35, column: 41, scope: !719)
!735 = !DILocalVariable(name: "status", scope: !637, file: !2, line: 36, type: !251)
!736 = !DILocation(line: 36, column: 14, scope: !637)
!737 = !DILocation(line: 36, column: 41, scope: !637)
!738 = !DILocation(line: 36, column: 47, scope: !637)
!739 = !DILocation(line: 36, column: 60, scope: !637)
!740 = !DILocation(line: 36, column: 68, scope: !637)
!741 = !DILocation(line: 36, column: 74, scope: !637)
!742 = !DILocation(line: 36, column: 81, scope: !637)
!743 = !DILocation(line: 36, column: 23, scope: !637)
!744 = !DILocation(line: 37, column: 5, scope: !637)
!745 = !DILocalVariable(name: "i", scope: !746, file: !2, line: 38, type: !251)
!746 = distinct !DILexicalBlock(scope: !637, file: !2, line: 38, column: 5)
!747 = !DILocation(line: 38, column: 19, scope: !746)
!748 = !DILocation(line: 38, column: 10, scope: !746)
!749 = !DILocation(line: 38, column: 26, scope: !750)
!750 = distinct !DILexicalBlock(scope: !746, file: !2, line: 38, column: 5)
!751 = !DILocation(line: 38, column: 28, scope: !750)
!752 = !DILocation(line: 38, column: 5, scope: !746)
!753 = !DILocation(line: 39, column: 9, scope: !754)
!754 = distinct !DILexicalBlock(scope: !750, file: !2, line: 38, column: 45)
!755 = !DILocation(line: 40, column: 9, scope: !754)
!756 = !DILocation(line: 38, column: 40, scope: !750)
!757 = !DILocation(line: 38, column: 5, scope: !750)
!758 = distinct !{!758, !752, !759, !701}
!759 = !DILocation(line: 41, column: 5, scope: !746)
!760 = !DILocalVariable(name: "i", scope: !761, file: !2, line: 43, type: !251)
!761 = distinct !DILexicalBlock(scope: !637, file: !2, line: 43, column: 5)
!762 = !DILocation(line: 43, column: 19, scope: !761)
!763 = !DILocation(line: 43, column: 10, scope: !761)
!764 = !DILocation(line: 43, column: 26, scope: !765)
!765 = distinct !DILexicalBlock(scope: !761, file: !2, line: 43, column: 5)
!766 = !DILocation(line: 43, column: 28, scope: !765)
!767 = !DILocation(line: 43, column: 5, scope: !761)
!768 = !DILocation(line: 44, column: 9, scope: !765)
!769 = !DILocation(line: 43, column: 34, scope: !765)
!770 = !DILocation(line: 43, column: 5, scope: !765)
!771 = distinct !{!771, !767, !772, !701}
!772 = !DILocation(line: 44, column: 9, scope: !761)
!773 = !DILocation(line: 45, column: 5, scope: !637)
!774 = distinct !DISubprogram(name: "main", scope: !32, file: !32, line: 6, type: !638, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !215, retainedNodes: !334)
!775 = !DILocalVariable(name: "result", scope: !774, file: !32, line: 8, type: !258)
!776 = !DILocation(line: 8, column: 9, scope: !774)
!777 = !DILocation(line: 8, column: 18, scope: !774)
!778 = !DILocalVariable(name: "completed", scope: !774, file: !32, line: 9, type: !779)
!779 = !DIBasicType(name: "unsigned char", size: 8, encoding: DW_ATE_unsigned_char)
!780 = !DILocation(line: 9, column: 19, scope: !774)
!781 = !DILocation(line: 11, column: 5, scope: !774)
!782 = !DILocation(line: 12, column: 12, scope: !774)
!783 = !DILocation(line: 12, column: 5, scope: !774)
!784 = distinct !DISubprogram(name: "__ubsan_handle_type_mismatch_v1", scope: !38, file: !38, line: 174, type: !785, scopeLine: 175, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!785 = !DISubroutineType(types: !786)
!786 = !{null, !787, !796}
!787 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !788, size: 64)
!788 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "TypeMismatchData", file: !317, line: 25, size: 256, flags: DIFlagTypePassByValue | DIFlagNonTrivial, elements: !789, identifier: "_ZTS16TypeMismatchData")
!789 = !{!790, !792, !794, !795}
!790 = !DIDerivedType(tag: DW_TAG_member, name: "Loc", scope: !788, file: !317, line: 26, baseType: !791, size: 128)
!791 = !DICompositeType(tag: DW_TAG_class_type, name: "SourceLocation", scope: !224, file: !222, line: 28, size: 128, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTSN7__ubsan14SourceLocationE")
!792 = !DIDerivedType(tag: DW_TAG_member, name: "Type", scope: !788, file: !317, line: 27, baseType: !793, size: 64, offset: 128)
!793 = !DIDerivedType(tag: DW_TAG_reference_type, baseType: !241, size: 64)
!794 = !DIDerivedType(tag: DW_TAG_member, name: "LogAlignment", scope: !788, file: !317, line: 28, baseType: !779, size: 8, offset: 192)
!795 = !DIDerivedType(tag: DW_TAG_member, name: "TypeCheckKind", scope: !788, file: !317, line: 29, baseType: !779, size: 8, offset: 200)
!796 = !DIDerivedType(tag: DW_TAG_typedef, name: "ValueHandle", scope: !224, file: !222, line: 78, baseType: !311)
!797 = !DILocalVariable(name: "Data", arg: 1, scope: !784, file: !38, line: 174, type: !787)
!798 = !DILocation(line: 174, column: 67, scope: !784)
!799 = !DILocalVariable(name: "Pointer", arg: 2, scope: !784, file: !38, line: 175, type: !796)
!800 = !DILocation(line: 175, column: 61, scope: !784)
!801 = !DILocation(line: 177, column: 26, scope: !784)
!802 = !DILocation(line: 177, column: 32, scope: !784)
!803 = !DILocation(line: 177, column: 3, scope: !784)
!804 = !DILocation(line: 178, column: 1, scope: !784)
!805 = distinct !DISubprogram(name: "handleTypeMismatchImpl", linkageName: "_ZN7__ubsanL22handleTypeMismatchImplEP16TypeMismatchDatam", scope: !224, file: !38, line: 158, type: !785, scopeLine: 159, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!806 = !DILocalVariable(name: "Data", arg: 1, scope: !805, file: !38, line: 158, type: !787)
!807 = !DILocation(line: 158, column: 54, scope: !805)
!808 = !DILocalVariable(name: "Pointer", arg: 2, scope: !805, file: !38, line: 159, type: !796)
!809 = !DILocation(line: 159, column: 48, scope: !805)
!810 = !DILocalVariable(name: "Alignment", scope: !805, file: !38, line: 160, type: !311)
!811 = !DILocation(line: 160, column: 8, scope: !805)
!812 = !DILocation(line: 160, column: 31, scope: !805)
!813 = !DILocation(line: 160, column: 37, scope: !805)
!814 = !DILocation(line: 160, column: 28, scope: !805)
!815 = !{!"True"}
!816 = !DILocalVariable(name: "ET", scope: !805, file: !38, line: 161, type: !256)
!817 = !DILocation(line: 161, column: 13, scope: !805)
!818 = !DILocation(line: 162, column: 8, scope: !819)
!819 = distinct !DILexicalBlock(scope: !805, file: !38, line: 162, column: 7)
!820 = !DILocation(line: 162, column: 7, scope: !805)
!821 = !DILocation(line: 163, column: 11, scope: !819)
!822 = !DILocation(line: 163, column: 17, scope: !819)
!823 = !DILocation(line: 163, column: 31, scope: !819)
!824 = !DILocation(line: 163, column: 10, scope: !819)
!825 = !DILocation(line: 163, column: 8, scope: !819)
!826 = !DILocation(line: 163, column: 5, scope: !819)
!827 = !DILocation(line: 166, column: 12, scope: !828)
!828 = distinct !DILexicalBlock(scope: !819, file: !38, line: 166, column: 12)
!829 = !DILocation(line: 166, column: 23, scope: !828)
!830 = !DILocation(line: 166, column: 33, scope: !828)
!831 = !DILocation(line: 166, column: 20, scope: !828)
!832 = !DILocation(line: 166, column: 12, scope: !819)
!833 = !DILocation(line: 167, column: 8, scope: !828)
!834 = !DILocation(line: 167, column: 5, scope: !828)
!835 = !DILocation(line: 169, column: 8, scope: !828)
!836 = !DILocation(line: 171, column: 21, scope: !805)
!837 = !DILocation(line: 171, column: 3, scope: !805)
!838 = distinct !DISubprogram(name: "report_error_type", linkageName: "_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE", scope: !224, file: !38, line: 115, type: !839, scopeLine: 115, flags: DIFlagPrototyped | DIFlagNoReturn, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!839 = !DISubroutineType(types: !840)
!840 = !{null, !256}
!841 = !DILocalVariable(name: "ET", arg: 1, scope: !838, file: !38, line: 115, type: !256)
!842 = !DILocation(line: 115, column: 67, scope: !838)
!843 = !DILocation(line: 116, column: 36, scope: !838)
!844 = !DILocation(line: 116, column: 16, scope: !838)
!845 = !DILocation(line: 116, column: 52, scope: !838)
!846 = !DILocation(line: 116, column: 41, scope: !838)
!847 = !DILocation(line: 116, column: 3, scope: !838)
!848 = distinct !DISubprogram(name: "ConvertTypeToString", linkageName: "_ZN7__ubsanL19ConvertTypeToStringENS_9ErrorTypeE", scope: !224, file: !38, line: 25, type: !849, scopeLine: 25, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!849 = !DISubroutineType(types: !850)
!850 = !{!239, !256}
!851 = !DILocalVariable(name: "Type", arg: 1, scope: !848, file: !38, line: 25, type: !256)
!852 = !DILocation(line: 25, column: 50, scope: !848)
!853 = !DILocation(line: 26, column: 11, scope: !848)
!854 = !DILocation(line: 26, column: 3, scope: !848)
!855 = !DILocation(line: 27, column: 1, scope: !856)
!856 = !DILexicalBlockFile(scope: !857, file: !53, discriminator: 0)
!857 = distinct !DILexicalBlock(scope: !848, file: !38, line: 26, column: 17)
!858 = !DILocation(line: 28, column: 1, scope: !856)
!859 = !DILocation(line: 29, column: 1, scope: !856)
!860 = !DILocation(line: 31, column: 1, scope: !856)
!861 = !DILocation(line: 32, column: 1, scope: !856)
!862 = !DILocation(line: 34, column: 1, scope: !856)
!863 = !DILocation(line: 36, column: 1, scope: !856)
!864 = !DILocation(line: 37, column: 1, scope: !856)
!865 = !DILocation(line: 38, column: 1, scope: !856)
!866 = !DILocation(line: 39, column: 1, scope: !856)
!867 = !DILocation(line: 40, column: 1, scope: !856)
!868 = !DILocation(line: 42, column: 1, scope: !856)
!869 = !DILocation(line: 44, column: 1, scope: !856)
!870 = !DILocation(line: 46, column: 1, scope: !856)
!871 = !DILocation(line: 47, column: 1, scope: !856)
!872 = !DILocation(line: 48, column: 1, scope: !856)
!873 = !DILocation(line: 49, column: 1, scope: !856)
!874 = !DILocation(line: 52, column: 1, scope: !856)
!875 = !DILocation(line: 55, column: 1, scope: !856)
!876 = !DILocation(line: 58, column: 1, scope: !856)
!877 = !DILocation(line: 61, column: 1, scope: !856)
!878 = !DILocation(line: 62, column: 1, scope: !856)
!879 = !DILocation(line: 63, column: 1, scope: !856)
!880 = !DILocation(line: 64, column: 1, scope: !856)
!881 = !DILocation(line: 65, column: 1, scope: !856)
!882 = !DILocation(line: 66, column: 1, scope: !856)
!883 = !DILocation(line: 67, column: 1, scope: !856)
!884 = !DILocation(line: 68, column: 1, scope: !856)
!885 = !DILocation(line: 69, column: 1, scope: !856)
!886 = !DILocation(line: 70, column: 1, scope: !856)
!887 = !DILocation(line: 71, column: 1, scope: !856)
!888 = !DILocation(line: 73, column: 1, scope: !856)
!889 = !DILocation(line: 75, column: 1, scope: !856)
!890 = !DILocation(line: 76, column: 1, scope: !856)
!891 = !DILocation(line: 78, column: 1, scope: !856)
!892 = !DILocation(line: 79, column: 1, scope: !856)
!893 = !DILocation(line: 32, column: 3, scope: !894)
!894 = !DILexicalBlockFile(scope: !857, file: !38, discriminator: 0)
!895 = !DILocation(line: 33, column: 1, scope: !848)
!896 = distinct !DISubprogram(name: "get_suffix", linkageName: "_ZN7__ubsanL10get_suffixENS_9ErrorTypeE", scope: !224, file: !38, line: 40, type: !849, scopeLine: 40, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!897 = !DILocalVariable(name: "ET", arg: 1, scope: !896, file: !38, line: 40, type: !256)
!898 = !DILocation(line: 40, column: 41, scope: !896)
!899 = !DILocation(line: 41, column: 11, scope: !896)
!900 = !DILocation(line: 41, column: 3, scope: !896)
!901 = !DILocation(line: 46, column: 5, scope: !902)
!902 = distinct !DILexicalBlock(scope: !896, file: !38, line: 41, column: 15)
!903 = !DILocation(line: 55, column: 5, scope: !902)
!904 = !DILocation(line: 59, column: 5, scope: !902)
!905 = !DILocation(line: 62, column: 5, scope: !902)
!906 = !DILocation(line: 65, column: 5, scope: !902)
!907 = !DILocation(line: 67, column: 5, scope: !902)
!908 = !DILocation(line: 71, column: 5, scope: !902)
!909 = !DILocation(line: 74, column: 5, scope: !902)
!910 = !DILocation(line: 77, column: 5, scope: !902)
!911 = !DILocation(line: 80, column: 5, scope: !902)
!912 = !DILocation(line: 82, column: 5, scope: !902)
!913 = !DILocation(line: 84, column: 5, scope: !902)
!914 = !DILocation(line: 86, column: 5, scope: !902)
!915 = !DILocation(line: 88, column: 5, scope: !902)
!916 = !DILocation(line: 90, column: 5, scope: !902)
!917 = !DILocation(line: 93, column: 5, scope: !902)
!918 = !DILocation(line: 96, column: 5, scope: !902)
!919 = !DILocation(line: 105, column: 5, scope: !902)
!920 = !DILocation(line: 109, column: 5, scope: !902)
!921 = !DILocation(line: 112, column: 5, scope: !902)
!922 = !DILocation(line: 114, column: 1, scope: !896)
!923 = distinct !DISubprogram(name: "report_error", linkageName: "_ZN7__ubsanL12report_errorEPKcS1_", scope: !224, file: !38, line: 35, type: !924, scopeLine: 36, flags: DIFlagPrototyped | DIFlagNoReturn, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!924 = !DISubroutineType(types: !925)
!925 = !{null, !239, !239}
!926 = !DILocalVariable(name: "msg", arg: 1, scope: !923, file: !38, line: 35, type: !239)
!927 = !DILocation(line: 35, column: 64, scope: !923)
!928 = !DILocalVariable(name: "suffix", arg: 2, scope: !923, file: !38, line: 36, type: !239)
!929 = !DILocation(line: 36, column: 64, scope: !923)
!930 = !DILocation(line: 37, column: 41, scope: !923)
!931 = !DILocation(line: 37, column: 46, scope: !923)
!932 = !DILocation(line: 37, column: 3, scope: !923)
!933 = distinct !DISubprogram(name: "__ubsan_handle_type_mismatch_v1_abort", scope: !38, file: !38, line: 180, type: !785, scopeLine: 181, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!934 = !DILocalVariable(name: "Data", arg: 1, scope: !933, file: !38, line: 180, type: !787)
!935 = !DILocation(line: 180, column: 73, scope: !933)
!936 = !DILocalVariable(name: "Pointer", arg: 2, scope: !933, file: !38, line: 181, type: !796)
!937 = !DILocation(line: 181, column: 67, scope: !933)
!938 = !DILocation(line: 183, column: 26, scope: !933)
!939 = !DILocation(line: 183, column: 32, scope: !933)
!940 = !DILocation(line: 183, column: 3, scope: !933)
!941 = !DILocation(line: 184, column: 1, scope: !933)
!942 = distinct !DISubprogram(name: "__ubsan_handle_alignment_assumption", scope: !38, file: !38, line: 195, type: !943, scopeLine: 197, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!943 = !DISubroutineType(types: !944)
!944 = !{null, !945, !796, !796, !796}
!945 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !946, size: 64)
!946 = !DICompositeType(tag: DW_TAG_structure_type, name: "AlignmentAssumptionData", file: !317, line: 32, size: 320, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS23AlignmentAssumptionData")
!947 = !DILocalVariable(name: "Data", arg: 1, scope: !942, file: !38, line: 195, type: !945)
!948 = !DILocation(line: 195, column: 62, scope: !942)
!949 = !DILocalVariable(name: "Pointer", arg: 2, scope: !942, file: !38, line: 196, type: !796)
!950 = !DILocation(line: 196, column: 49, scope: !942)
!951 = !DILocalVariable(name: "Alignment", arg: 3, scope: !942, file: !38, line: 196, type: !796)
!952 = !DILocation(line: 196, column: 70, scope: !942)
!953 = !DILocalVariable(name: "Offset", arg: 4, scope: !942, file: !38, line: 197, type: !796)
!954 = !DILocation(line: 197, column: 49, scope: !942)
!955 = !DILocation(line: 198, column: 33, scope: !942)
!956 = !DILocation(line: 198, column: 39, scope: !942)
!957 = !DILocation(line: 198, column: 48, scope: !942)
!958 = !DILocation(line: 198, column: 59, scope: !942)
!959 = !DILocation(line: 198, column: 3, scope: !942)
!960 = !DILocation(line: 199, column: 1, scope: !942)
!961 = distinct !DISubprogram(name: "handleAlignmentAssumptionImpl", linkageName: "_ZN7__ubsanL29handleAlignmentAssumptionImplEP23AlignmentAssumptionDatammm", scope: !224, file: !38, line: 186, type: !943, scopeLine: 189, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!962 = !DILocalVariable(arg: 1, scope: !961, file: !38, line: 186, type: !945)
!963 = !DILocation(line: 186, column: 77, scope: !961)
!964 = !DILocalVariable(arg: 2, scope: !961, file: !38, line: 187, type: !796)
!965 = !DILocation(line: 187, column: 66, scope: !961)
!966 = !DILocalVariable(arg: 3, scope: !961, file: !38, line: 188, type: !796)
!967 = !DILocation(line: 188, column: 68, scope: !961)
!968 = !DILocalVariable(arg: 4, scope: !961, file: !38, line: 189, type: !796)
!969 = !DILocation(line: 189, column: 65, scope: !961)
!970 = !DILocalVariable(name: "ET", scope: !961, file: !38, line: 190, type: !256)
!971 = !DILocation(line: 190, column: 13, scope: !961)
!972 = !DILocation(line: 191, column: 21, scope: !961)
!973 = !DILocation(line: 191, column: 3, scope: !961)
!974 = distinct !DISubprogram(name: "__ubsan_handle_alignment_assumption_abort", scope: !38, file: !38, line: 201, type: !943, scopeLine: 203, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!975 = !DILocalVariable(name: "Data", arg: 1, scope: !974, file: !38, line: 202, type: !945)
!976 = !DILocation(line: 202, column: 30, scope: !974)
!977 = !DILocalVariable(name: "Pointer", arg: 2, scope: !974, file: !38, line: 202, type: !796)
!978 = !DILocation(line: 202, column: 48, scope: !974)
!979 = !DILocalVariable(name: "Alignment", arg: 3, scope: !974, file: !38, line: 202, type: !796)
!980 = !DILocation(line: 202, column: 69, scope: !974)
!981 = !DILocalVariable(name: "Offset", arg: 4, scope: !974, file: !38, line: 203, type: !796)
!982 = !DILocation(line: 203, column: 17, scope: !974)
!983 = !DILocation(line: 204, column: 33, scope: !974)
!984 = !DILocation(line: 204, column: 39, scope: !974)
!985 = !DILocation(line: 204, column: 48, scope: !974)
!986 = !DILocation(line: 204, column: 59, scope: !974)
!987 = !DILocation(line: 204, column: 3, scope: !974)
!988 = !DILocation(line: 205, column: 1, scope: !974)
!989 = distinct !DISubprogram(name: "__ubsan_handle_add_overflow", scope: !38, file: !38, line: 222, type: !990, scopeLine: 222, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!990 = !DISubroutineType(types: !991)
!991 = !{null, !992, !796, !796}
!992 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !993, size: 64)
!993 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "OverflowData", file: !317, line: 38, size: 192, flags: DIFlagTypePassByValue | DIFlagNonTrivial, elements: !994, identifier: "_ZTS12OverflowData")
!994 = !{!995, !996}
!995 = !DIDerivedType(tag: DW_TAG_member, name: "Loc", scope: !993, file: !317, line: 39, baseType: !791, size: 128)
!996 = !DIDerivedType(tag: DW_TAG_member, name: "Type", scope: !993, file: !317, line: 40, baseType: !793, size: 64, offset: 128)
!997 = !DILocalVariable(name: "Data", arg: 1, scope: !989, file: !38, line: 222, type: !992)
!998 = !DILocation(line: 222, column: 1, scope: !989)
!999 = !DILocalVariable(name: "LHS", arg: 2, scope: !989, file: !38, line: 222, type: !796)
!1000 = !DILocalVariable(name: "RHS", arg: 3, scope: !989, file: !38, line: 222, type: !796)
!1001 = distinct !DISubprogram(name: "handleIntegerOverflowImpl", linkageName: "_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc", scope: !224, file: !38, line: 208, type: !1002, scopeLine: 209, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1002 = !DISubroutineType(types: !1003)
!1003 = !{null, !992, !796, !239}
!1004 = !DILocalVariable(name: "Data", arg: 1, scope: !1001, file: !38, line: 208, type: !992)
!1005 = !DILocation(line: 208, column: 53, scope: !1001)
!1006 = !DILocalVariable(arg: 2, scope: !1001, file: !38, line: 208, type: !796)
!1007 = !DILocation(line: 208, column: 78, scope: !1001)
!1008 = !DILocalVariable(arg: 3, scope: !1001, file: !38, line: 209, type: !239)
!1009 = !DILocation(line: 209, column: 64, scope: !1001)
!1010 = !DILocalVariable(name: "IsSigned", scope: !1001, file: !38, line: 210, type: !248)
!1011 = !DILocation(line: 210, column: 8, scope: !1001)
!1012 = !DILocation(line: 210, column: 19, scope: !1001)
!1013 = !DILocation(line: 210, column: 25, scope: !1001)
!1014 = !DILocation(line: 210, column: 30, scope: !1001)
!1015 = !DILocalVariable(name: "ET", scope: !1001, file: !38, line: 211, type: !256)
!1016 = !DILocation(line: 211, column: 13, scope: !1001)
!1017 = !DILocation(line: 211, column: 18, scope: !1001)
!1018 = !DILocation(line: 213, column: 21, scope: !1001)
!1019 = !DILocation(line: 213, column: 3, scope: !1001)
!1020 = distinct !DISubprogram(name: "isSignedIntegerTy", linkageName: "_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv", scope: !223, file: !222, line: 73, type: !246, scopeLine: 73, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, declaration: !249, retainedNodes: !334)
!1021 = !DILocalVariable(name: "this", arg: 1, scope: !1020, type: !1022, flags: DIFlagArtificial | DIFlagObjectPointer)
!1022 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !241, size: 64)
!1023 = !DILocation(line: 0, scope: !1020)
!1024 = !DILocation(line: 73, column: 43, scope: !1020)
!1025 = !DILocation(line: 73, column: 57, scope: !1020)
!1026 = !DILocation(line: 73, column: 61, scope: !1020)
!1027 = !DILocation(line: 73, column: 70, scope: !1020)
!1028 = !DILocation(line: 73, column: 60, scope: !1020)
!1029 = !DILocation(line: 73, column: 36, scope: !1020)
!1030 = distinct !DISubprogram(name: "isIntegerTy", linkageName: "_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv", scope: !223, file: !222, line: 72, type: !246, scopeLine: 72, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, declaration: !245, retainedNodes: !334)
!1031 = !DILocalVariable(name: "this", arg: 1, scope: !1030, type: !1022, flags: DIFlagArtificial | DIFlagObjectPointer)
!1032 = !DILocation(line: 0, scope: !1030)
!1033 = !DILocation(line: 72, column: 37, scope: !1030)
!1034 = !DILocation(line: 72, column: 47, scope: !1030)
!1035 = !DILocation(line: 72, column: 30, scope: !1030)
!1036 = distinct !DISubprogram(name: "getKind", linkageName: "_ZNK7__ubsan14TypeDescriptor7getKindEv", scope: !223, file: !222, line: 70, type: !243, scopeLine: 70, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, declaration: !242, retainedNodes: !334)
!1037 = !DILocalVariable(name: "this", arg: 1, scope: !1036, type: !1022, flags: DIFlagArtificial | DIFlagObjectPointer)
!1038 = !DILocation(line: 0, scope: !1036)
!1039 = !DILocation(line: 70, column: 51, scope: !1036)
!1040 = !DILocation(line: 70, column: 33, scope: !1036)
!1041 = !DILocation(line: 70, column: 26, scope: !1036)
!1042 = distinct !DISubprogram(name: "__ubsan_handle_add_overflow_abort", scope: !38, file: !38, line: 223, type: !990, scopeLine: 223, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1043 = !DILocalVariable(name: "Data", arg: 1, scope: !1042, file: !38, line: 223, type: !992)
!1044 = !DILocation(line: 223, column: 1, scope: !1042)
!1045 = !DILocalVariable(name: "LHS", arg: 2, scope: !1042, file: !38, line: 223, type: !796)
!1046 = !DILocalVariable(name: "RHS", arg: 3, scope: !1042, file: !38, line: 223, type: !796)
!1047 = distinct !DISubprogram(name: "__ubsan_handle_sub_overflow", scope: !38, file: !38, line: 224, type: !990, scopeLine: 224, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1048 = !DILocalVariable(name: "Data", arg: 1, scope: !1047, file: !38, line: 224, type: !992)
!1049 = !DILocation(line: 224, column: 1, scope: !1047)
!1050 = !DILocalVariable(name: "LHS", arg: 2, scope: !1047, file: !38, line: 224, type: !796)
!1051 = !DILocalVariable(name: "RHS", arg: 3, scope: !1047, file: !38, line: 224, type: !796)
!1052 = distinct !DISubprogram(name: "__ubsan_handle_sub_overflow_abort", scope: !38, file: !38, line: 225, type: !990, scopeLine: 225, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1053 = !DILocalVariable(name: "Data", arg: 1, scope: !1052, file: !38, line: 225, type: !992)
!1054 = !DILocation(line: 225, column: 1, scope: !1052)
!1055 = !DILocalVariable(name: "LHS", arg: 2, scope: !1052, file: !38, line: 225, type: !796)
!1056 = !DILocalVariable(name: "RHS", arg: 3, scope: !1052, file: !38, line: 225, type: !796)
!1057 = distinct !DISubprogram(name: "__ubsan_handle_mul_overflow", scope: !38, file: !38, line: 226, type: !990, scopeLine: 226, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1058 = !DILocalVariable(name: "Data", arg: 1, scope: !1057, file: !38, line: 226, type: !992)
!1059 = !DILocation(line: 226, column: 1, scope: !1057)
!1060 = !DILocalVariable(name: "LHS", arg: 2, scope: !1057, file: !38, line: 226, type: !796)
!1061 = !DILocalVariable(name: "RHS", arg: 3, scope: !1057, file: !38, line: 226, type: !796)
!1062 = distinct !DISubprogram(name: "__ubsan_handle_mul_overflow_abort", scope: !38, file: !38, line: 227, type: !990, scopeLine: 227, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1063 = !DILocalVariable(name: "Data", arg: 1, scope: !1062, file: !38, line: 227, type: !992)
!1064 = !DILocation(line: 227, column: 1, scope: !1062)
!1065 = !DILocalVariable(name: "LHS", arg: 2, scope: !1062, file: !38, line: 227, type: !796)
!1066 = !DILocalVariable(name: "RHS", arg: 3, scope: !1062, file: !38, line: 227, type: !796)
!1067 = distinct !DISubprogram(name: "__ubsan_handle_negate_overflow", scope: !38, file: !38, line: 237, type: !1068, scopeLine: 238, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1068 = !DISubroutineType(types: !1069)
!1069 = !{null, !992, !796}
!1070 = !DILocalVariable(name: "Data", arg: 1, scope: !1067, file: !38, line: 237, type: !992)
!1071 = !DILocation(line: 237, column: 62, scope: !1067)
!1072 = !DILocalVariable(name: "OldVal", arg: 2, scope: !1067, file: !38, line: 238, type: !796)
!1073 = !DILocation(line: 238, column: 60, scope: !1067)
!1074 = !DILocation(line: 239, column: 28, scope: !1067)
!1075 = !DILocation(line: 239, column: 34, scope: !1067)
!1076 = !DILocation(line: 239, column: 3, scope: !1067)
!1077 = !DILocation(line: 240, column: 1, scope: !1067)
!1078 = distinct !DISubprogram(name: "handleNegateOverflowImpl", linkageName: "_ZN7__ubsanL24handleNegateOverflowImplEP12OverflowDatam", scope: !224, file: !38, line: 229, type: !1068, scopeLine: 230, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1079 = !DILocalVariable(name: "Data", arg: 1, scope: !1078, file: !38, line: 229, type: !992)
!1080 = !DILocation(line: 229, column: 52, scope: !1078)
!1081 = !DILocalVariable(arg: 2, scope: !1078, file: !38, line: 230, type: !796)
!1082 = !DILocation(line: 230, column: 60, scope: !1078)
!1083 = !DILocalVariable(name: "IsSigned", scope: !1078, file: !38, line: 231, type: !248)
!1084 = !DILocation(line: 231, column: 8, scope: !1078)
!1085 = !DILocation(line: 231, column: 19, scope: !1078)
!1086 = !DILocation(line: 231, column: 25, scope: !1078)
!1087 = !DILocation(line: 231, column: 30, scope: !1078)
!1088 = !DILocalVariable(name: "ET", scope: !1078, file: !38, line: 232, type: !256)
!1089 = !DILocation(line: 232, column: 13, scope: !1078)
!1090 = !DILocation(line: 232, column: 18, scope: !1078)
!1091 = !DILocation(line: 234, column: 21, scope: !1078)
!1092 = !DILocation(line: 234, column: 3, scope: !1078)
!1093 = distinct !DISubprogram(name: "__ubsan_handle_negate_overflow_abort", scope: !38, file: !38, line: 242, type: !1068, scopeLine: 243, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1094 = !DILocalVariable(name: "Data", arg: 1, scope: !1093, file: !38, line: 242, type: !992)
!1095 = !DILocation(line: 242, column: 68, scope: !1093)
!1096 = !DILocalVariable(name: "OldVal", arg: 2, scope: !1093, file: !38, line: 243, type: !796)
!1097 = !DILocation(line: 243, column: 66, scope: !1093)
!1098 = !DILocation(line: 244, column: 28, scope: !1093)
!1099 = !DILocation(line: 244, column: 34, scope: !1093)
!1100 = !DILocation(line: 244, column: 3, scope: !1093)
!1101 = !DILocation(line: 245, column: 1, scope: !1093)
!1102 = distinct !DISubprogram(name: "__ubsan_handle_divrem_overflow", scope: !38, file: !38, line: 257, type: !990, scopeLine: 259, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1103 = !DILocalVariable(name: "Data", arg: 1, scope: !1102, file: !38, line: 257, type: !992)
!1104 = !DILocation(line: 257, column: 62, scope: !1102)
!1105 = !DILocalVariable(name: "LHS", arg: 2, scope: !1102, file: !38, line: 258, type: !796)
!1106 = !DILocation(line: 258, column: 60, scope: !1102)
!1107 = !DILocalVariable(name: "RHS", arg: 3, scope: !1102, file: !38, line: 259, type: !796)
!1108 = !DILocation(line: 259, column: 60, scope: !1102)
!1109 = !DILocation(line: 260, column: 28, scope: !1102)
!1110 = !DILocation(line: 260, column: 34, scope: !1102)
!1111 = !DILocation(line: 260, column: 39, scope: !1102)
!1112 = !DILocation(line: 260, column: 3, scope: !1102)
!1113 = !DILocation(line: 261, column: 1, scope: !1102)
!1114 = distinct !DISubprogram(name: "handleDivremOverflowImpl", linkageName: "_ZN7__ubsanL24handleDivremOverflowImplEP12OverflowDatamm", scope: !224, file: !38, line: 247, type: !990, scopeLine: 248, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1115 = !DILocalVariable(name: "Data", arg: 1, scope: !1114, file: !38, line: 247, type: !992)
!1116 = !DILocation(line: 247, column: 52, scope: !1114)
!1117 = !DILocalVariable(arg: 2, scope: !1114, file: !38, line: 247, type: !796)
!1118 = !DILocation(line: 247, column: 77, scope: !1114)
!1119 = !DILocalVariable(arg: 3, scope: !1114, file: !38, line: 248, type: !796)
!1120 = !DILocation(line: 248, column: 57, scope: !1114)
!1121 = !DILocation(line: 249, column: 7, scope: !1122)
!1122 = distinct !DILexicalBlock(scope: !1114, file: !38, line: 249, column: 7)
!1123 = !DILocation(line: 249, column: 13, scope: !1122)
!1124 = !DILocation(line: 249, column: 18, scope: !1122)
!1125 = !DILocation(line: 249, column: 7, scope: !1114)
!1126 = !DILocation(line: 250, column: 5, scope: !1122)
!1127 = !DILocalVariable(name: "ET", scope: !1128, file: !38, line: 252, type: !256)
!1128 = distinct !DILexicalBlock(scope: !1122, file: !38, line: 251, column: 8)
!1129 = !DILocation(line: 252, column: 15, scope: !1128)
!1130 = !DILocation(line: 253, column: 23, scope: !1128)
!1131 = !DILocation(line: 253, column: 5, scope: !1128)
!1132 = distinct !DISubprogram(name: "__ubsan_handle_divrem_overflow_abort", scope: !38, file: !38, line: 263, type: !990, scopeLine: 265, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1133 = !DILocalVariable(name: "Data", arg: 1, scope: !1132, file: !38, line: 263, type: !992)
!1134 = !DILocation(line: 263, column: 68, scope: !1132)
!1135 = !DILocalVariable(name: "LHS", arg: 2, scope: !1132, file: !38, line: 264, type: !796)
!1136 = !DILocation(line: 264, column: 66, scope: !1132)
!1137 = !DILocalVariable(name: "RHS", arg: 3, scope: !1132, file: !38, line: 265, type: !796)
!1138 = !DILocation(line: 265, column: 66, scope: !1132)
!1139 = !DILocation(line: 266, column: 28, scope: !1132)
!1140 = !DILocation(line: 266, column: 34, scope: !1132)
!1141 = !DILocation(line: 266, column: 39, scope: !1132)
!1142 = !DILocation(line: 266, column: 3, scope: !1132)
!1143 = !DILocation(line: 267, column: 1, scope: !1132)
!1144 = distinct !DISubprogram(name: "__ubsan_handle_shift_out_of_bounds", scope: !38, file: !38, line: 275, type: !1145, scopeLine: 277, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1145 = !DISubroutineType(types: !1146)
!1146 = !{null, !1147, !796, !796}
!1147 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1148, size: 64)
!1148 = !DICompositeType(tag: DW_TAG_structure_type, name: "ShiftOutOfBoundsData", file: !317, line: 43, size: 256, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS20ShiftOutOfBoundsData")
!1149 = !DILocalVariable(name: "Data", arg: 1, scope: !1144, file: !38, line: 275, type: !1147)
!1150 = !DILocation(line: 275, column: 74, scope: !1144)
!1151 = !DILocalVariable(name: "LHS", arg: 2, scope: !1144, file: !38, line: 276, type: !796)
!1152 = !DILocation(line: 276, column: 64, scope: !1144)
!1153 = !DILocalVariable(name: "RHS", arg: 3, scope: !1144, file: !38, line: 277, type: !796)
!1154 = !DILocation(line: 277, column: 64, scope: !1144)
!1155 = !DILocation(line: 278, column: 30, scope: !1144)
!1156 = !DILocation(line: 278, column: 36, scope: !1144)
!1157 = !DILocation(line: 278, column: 41, scope: !1144)
!1158 = !DILocation(line: 278, column: 3, scope: !1144)
!1159 = !DILocation(line: 279, column: 1, scope: !1144)
!1160 = distinct !DISubprogram(name: "handleShiftOutOfBoundsImpl", linkageName: "_ZN7__ubsanL26handleShiftOutOfBoundsImplEP20ShiftOutOfBoundsDatamm", scope: !224, file: !38, line: 269, type: !1145, scopeLine: 271, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1161 = !DILocalVariable(arg: 1, scope: !1160, file: !38, line: 269, type: !1147)
!1162 = !DILocation(line: 269, column: 71, scope: !1160)
!1163 = !DILocalVariable(arg: 2, scope: !1160, file: !38, line: 270, type: !796)
!1164 = !DILocation(line: 270, column: 59, scope: !1160)
!1165 = !DILocalVariable(arg: 3, scope: !1160, file: !38, line: 271, type: !796)
!1166 = !DILocation(line: 271, column: 59, scope: !1160)
!1167 = !DILocation(line: 272, column: 3, scope: !1160)
!1168 = distinct !DISubprogram(name: "__ubsan_handle_shift_out_of_bounds_abort", scope: !38, file: !38, line: 282, type: !1145, scopeLine: 283, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1169 = !DILocalVariable(name: "Data", arg: 1, scope: !1168, file: !38, line: 282, type: !1147)
!1170 = !DILocation(line: 282, column: 64, scope: !1168)
!1171 = !DILocalVariable(name: "LHS", arg: 2, scope: !1168, file: !38, line: 283, type: !796)
!1172 = !DILocation(line: 283, column: 54, scope: !1168)
!1173 = !DILocalVariable(name: "RHS", arg: 3, scope: !1168, file: !38, line: 283, type: !796)
!1174 = !DILocation(line: 283, column: 71, scope: !1168)
!1175 = !DILocation(line: 284, column: 30, scope: !1168)
!1176 = !DILocation(line: 284, column: 36, scope: !1168)
!1177 = !DILocation(line: 284, column: 41, scope: !1168)
!1178 = !DILocation(line: 284, column: 3, scope: !1168)
!1179 = !DILocation(line: 285, column: 1, scope: !1168)
!1180 = distinct !DISubprogram(name: "__ubsan_handle_out_of_bounds", scope: !38, file: !38, line: 293, type: !1181, scopeLine: 294, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1181 = !DISubroutineType(types: !1182)
!1182 = !{null, !1183, !796}
!1183 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1184, size: 64)
!1184 = !DICompositeType(tag: DW_TAG_structure_type, name: "OutOfBoundsData", file: !317, line: 49, size: 256, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS15OutOfBoundsData")
!1185 = !DILocalVariable(name: "Data", arg: 1, scope: !1180, file: !38, line: 293, type: !1183)
!1186 = !DILocation(line: 293, column: 63, scope: !1180)
!1187 = !DILocalVariable(name: "Index", arg: 2, scope: !1180, file: !38, line: 294, type: !796)
!1188 = !DILocation(line: 294, column: 58, scope: !1180)
!1189 = !DILocation(line: 295, column: 25, scope: !1180)
!1190 = !DILocation(line: 295, column: 31, scope: !1180)
!1191 = !DILocation(line: 295, column: 3, scope: !1180)
!1192 = !DILocation(line: 296, column: 1, scope: !1180)
!1193 = distinct !DISubprogram(name: "handleOutOfBoundsImpl", linkageName: "_ZN7__ubsanL21handleOutOfBoundsImplEP15OutOfBoundsDatam", scope: !224, file: !38, line: 287, type: !1181, scopeLine: 288, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1194 = !DILocalVariable(arg: 1, scope: !1193, file: !38, line: 287, type: !1183)
!1195 = !DILocation(line: 287, column: 61, scope: !1193)
!1196 = !DILocalVariable(arg: 2, scope: !1193, file: !38, line: 288, type: !796)
!1197 = !DILocation(line: 288, column: 56, scope: !1193)
!1198 = !DILocalVariable(name: "ET", scope: !1193, file: !38, line: 289, type: !256)
!1199 = !DILocation(line: 289, column: 13, scope: !1193)
!1200 = !DILocation(line: 290, column: 21, scope: !1193)
!1201 = !DILocation(line: 290, column: 3, scope: !1193)
!1202 = distinct !DISubprogram(name: "__ubsan_handle_out_of_bounds_abort", scope: !38, file: !38, line: 298, type: !1181, scopeLine: 299, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1203 = !DILocalVariable(name: "Data", arg: 1, scope: !1202, file: !38, line: 298, type: !1183)
!1204 = !DILocation(line: 298, column: 69, scope: !1202)
!1205 = !DILocalVariable(name: "Index", arg: 2, scope: !1202, file: !38, line: 299, type: !796)
!1206 = !DILocation(line: 299, column: 64, scope: !1202)
!1207 = !DILocation(line: 300, column: 25, scope: !1202)
!1208 = !DILocation(line: 300, column: 31, scope: !1202)
!1209 = !DILocation(line: 300, column: 3, scope: !1202)
!1210 = !DILocation(line: 301, column: 1, scope: !1202)
!1211 = distinct !DISubprogram(name: "__ubsan_handle_builtin_unreachable", scope: !38, file: !38, line: 308, type: !1212, scopeLine: 308, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1212 = !DISubroutineType(types: !1213)
!1213 = !{null, !1214}
!1214 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1215, size: 64)
!1215 = !DICompositeType(tag: DW_TAG_structure_type, name: "UnreachableData", file: !317, line: 55, size: 128, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS15UnreachableData")
!1216 = !DILocalVariable(name: "Data", arg: 1, scope: !1211, file: !38, line: 308, type: !1214)
!1217 = !DILocation(line: 308, column: 69, scope: !1211)
!1218 = !DILocation(line: 309, column: 32, scope: !1211)
!1219 = !DILocation(line: 309, column: 3, scope: !1211)
!1220 = !DILocation(line: 310, column: 1, scope: !1211)
!1221 = distinct !DISubprogram(name: "handleBuiltinUnreachableImpl", linkageName: "_ZN7__ubsanL28handleBuiltinUnreachableImplEP15UnreachableData", scope: !224, file: !38, line: 303, type: !1212, scopeLine: 303, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1222 = !DILocalVariable(arg: 1, scope: !1221, file: !38, line: 303, type: !1214)
!1223 = !DILocation(line: 303, column: 68, scope: !1221)
!1224 = !DILocalVariable(name: "ET", scope: !1221, file: !38, line: 304, type: !256)
!1225 = !DILocation(line: 304, column: 13, scope: !1221)
!1226 = !DILocation(line: 305, column: 21, scope: !1221)
!1227 = !DILocation(line: 305, column: 3, scope: !1221)
!1228 = distinct !DISubprogram(name: "__ubsan_handle_missing_return", scope: !38, file: !38, line: 317, type: !1212, scopeLine: 317, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1229 = !DILocalVariable(name: "Data", arg: 1, scope: !1228, file: !38, line: 317, type: !1214)
!1230 = !DILocation(line: 317, column: 64, scope: !1228)
!1231 = !DILocation(line: 318, column: 27, scope: !1228)
!1232 = !DILocation(line: 318, column: 3, scope: !1228)
!1233 = !DILocation(line: 319, column: 1, scope: !1228)
!1234 = distinct !DISubprogram(name: "handleMissingReturnImpl", linkageName: "_ZN7__ubsanL23handleMissingReturnImplEP15UnreachableData", scope: !224, file: !38, line: 312, type: !1212, scopeLine: 312, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1235 = !DILocalVariable(arg: 1, scope: !1234, file: !38, line: 312, type: !1214)
!1236 = !DILocation(line: 312, column: 63, scope: !1234)
!1237 = !DILocalVariable(name: "ET", scope: !1234, file: !38, line: 313, type: !256)
!1238 = !DILocation(line: 313, column: 13, scope: !1234)
!1239 = !DILocation(line: 314, column: 21, scope: !1234)
!1240 = !DILocation(line: 314, column: 3, scope: !1234)
!1241 = distinct !DISubprogram(name: "__ubsan_handle_vla_bound_not_positive", scope: !38, file: !38, line: 327, type: !1242, scopeLine: 328, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1242 = !DISubroutineType(types: !1243)
!1243 = !{null, !1244, !796}
!1244 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1245, size: 64)
!1245 = !DICompositeType(tag: DW_TAG_structure_type, name: "VLABoundData", file: !317, line: 59, size: 192, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS12VLABoundData")
!1246 = !DILocalVariable(name: "Data", arg: 1, scope: !1241, file: !38, line: 327, type: !1244)
!1247 = !DILocation(line: 327, column: 69, scope: !1241)
!1248 = !DILocalVariable(name: "Bound", arg: 2, scope: !1241, file: !38, line: 328, type: !796)
!1249 = !DILocation(line: 328, column: 67, scope: !1241)
!1250 = !DILocation(line: 329, column: 29, scope: !1241)
!1251 = !DILocation(line: 329, column: 35, scope: !1241)
!1252 = !DILocation(line: 329, column: 3, scope: !1241)
!1253 = !DILocation(line: 330, column: 1, scope: !1241)
!1254 = distinct !DISubprogram(name: "handleVLABoundNotPositive", linkageName: "_ZN7__ubsanL25handleVLABoundNotPositiveEP12VLABoundDatam", scope: !224, file: !38, line: 321, type: !1242, scopeLine: 322, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1255 = !DILocalVariable(arg: 1, scope: !1254, file: !38, line: 321, type: !1244)
!1256 = !DILocation(line: 321, column: 62, scope: !1254)
!1257 = !DILocalVariable(arg: 2, scope: !1254, file: !38, line: 322, type: !796)
!1258 = !DILocation(line: 322, column: 60, scope: !1254)
!1259 = !DILocalVariable(name: "ET", scope: !1254, file: !38, line: 323, type: !256)
!1260 = !DILocation(line: 323, column: 13, scope: !1254)
!1261 = !DILocation(line: 324, column: 21, scope: !1254)
!1262 = !DILocation(line: 324, column: 3, scope: !1254)
!1263 = distinct !DISubprogram(name: "__ubsan_handle_vla_bound_not_positive_abort", scope: !38, file: !38, line: 332, type: !1242, scopeLine: 333, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1264 = !DILocalVariable(name: "Data", arg: 1, scope: !1263, file: !38, line: 332, type: !1244)
!1265 = !DILocation(line: 332, column: 75, scope: !1263)
!1266 = !DILocalVariable(name: "Bound", arg: 2, scope: !1263, file: !38, line: 333, type: !796)
!1267 = !DILocation(line: 333, column: 73, scope: !1263)
!1268 = !DILocation(line: 334, column: 29, scope: !1263)
!1269 = !DILocation(line: 334, column: 35, scope: !1263)
!1270 = !DILocation(line: 334, column: 3, scope: !1263)
!1271 = !DILocation(line: 335, column: 1, scope: !1263)
!1272 = distinct !DISubprogram(name: "__ubsan_handle_float_cast_overflow", scope: !38, file: !38, line: 342, type: !1273, scopeLine: 343, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1273 = !DISubroutineType(types: !1274)
!1274 = !{null, !1275, !796}
!1275 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)
!1276 = !DILocalVariable(name: "Data", arg: 1, scope: !1272, file: !38, line: 342, type: !1275)
!1277 = !DILocation(line: 342, column: 58, scope: !1272)
!1278 = !DILocalVariable(name: "From", arg: 2, scope: !1272, file: !38, line: 343, type: !796)
!1279 = !DILocation(line: 343, column: 64, scope: !1272)
!1280 = !DILocation(line: 344, column: 27, scope: !1272)
!1281 = !DILocation(line: 344, column: 33, scope: !1272)
!1282 = !DILocation(line: 344, column: 3, scope: !1272)
!1283 = !DILocation(line: 345, column: 1, scope: !1272)
!1284 = distinct !DISubprogram(name: "handleFloatCastOverflow", linkageName: "_ZN7__ubsanL23handleFloatCastOverflowEPvm", scope: !224, file: !38, line: 337, type: !1273, scopeLine: 337, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1285 = !DILocalVariable(arg: 1, scope: !1284, file: !38, line: 337, type: !1275)
!1286 = !DILocation(line: 337, column: 55, scope: !1284)
!1287 = !DILocalVariable(arg: 2, scope: !1284, file: !38, line: 337, type: !796)
!1288 = !DILocation(line: 337, column: 77, scope: !1284)
!1289 = !DILocalVariable(name: "ET", scope: !1284, file: !38, line: 338, type: !256)
!1290 = !DILocation(line: 338, column: 13, scope: !1284)
!1291 = !DILocation(line: 339, column: 21, scope: !1284)
!1292 = !DILocation(line: 339, column: 3, scope: !1284)
!1293 = distinct !DISubprogram(name: "__ubsan_handle_float_cast_overflow_abort", scope: !38, file: !38, line: 347, type: !1273, scopeLine: 348, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1294 = !DILocalVariable(name: "Data", arg: 1, scope: !1293, file: !38, line: 347, type: !1275)
!1295 = !DILocation(line: 347, column: 64, scope: !1293)
!1296 = !DILocalVariable(name: "From", arg: 2, scope: !1293, file: !38, line: 348, type: !796)
!1297 = !DILocation(line: 348, column: 70, scope: !1293)
!1298 = !DILocation(line: 349, column: 27, scope: !1293)
!1299 = !DILocation(line: 349, column: 33, scope: !1293)
!1300 = !DILocation(line: 349, column: 3, scope: !1293)
!1301 = !DILocation(line: 350, column: 1, scope: !1293)
!1302 = distinct !DISubprogram(name: "__ubsan_handle_load_invalid_value", scope: !38, file: !38, line: 357, type: !1303, scopeLine: 358, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1303 = !DISubroutineType(types: !1304)
!1304 = !{null, !1305, !796}
!1305 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1306, size: 64)
!1306 = !DICompositeType(tag: DW_TAG_structure_type, name: "InvalidValueData", file: !317, line: 64, size: 192, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS16InvalidValueData")
!1307 = !DILocalVariable(name: "Data", arg: 1, scope: !1302, file: !38, line: 357, type: !1305)
!1308 = !DILocation(line: 357, column: 69, scope: !1302)
!1309 = !DILocalVariable(name: "Val", arg: 2, scope: !1302, file: !38, line: 358, type: !796)
!1310 = !DILocation(line: 358, column: 63, scope: !1302)
!1311 = !DILocation(line: 359, column: 26, scope: !1302)
!1312 = !DILocation(line: 359, column: 32, scope: !1302)
!1313 = !DILocation(line: 359, column: 3, scope: !1302)
!1314 = !DILocation(line: 360, column: 1, scope: !1302)
!1315 = distinct !DISubprogram(name: "handleLoadInvalidValue", linkageName: "_ZN7__ubsanL22handleLoadInvalidValueEP16InvalidValueDatam", scope: !224, file: !38, line: 352, type: !1303, scopeLine: 353, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1316 = !DILocalVariable(arg: 1, scope: !1315, file: !38, line: 352, type: !1305)
!1317 = !DILocation(line: 352, column: 63, scope: !1315)
!1318 = !DILocalVariable(arg: 2, scope: !1315, file: !38, line: 353, type: !796)
!1319 = !DILocation(line: 353, column: 55, scope: !1315)
!1320 = !DILocation(line: 354, column: 3, scope: !1315)
!1321 = distinct !DISubprogram(name: "__ubsan_handle_load_invalid_value_abort", scope: !38, file: !38, line: 361, type: !1303, scopeLine: 362, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1322 = !DILocalVariable(name: "Data", arg: 1, scope: !1321, file: !38, line: 361, type: !1305)
!1323 = !DILocation(line: 361, column: 75, scope: !1321)
!1324 = !DILocalVariable(name: "Val", arg: 2, scope: !1321, file: !38, line: 362, type: !796)
!1325 = !DILocation(line: 362, column: 69, scope: !1321)
!1326 = !DILocation(line: 363, column: 26, scope: !1321)
!1327 = !DILocation(line: 363, column: 32, scope: !1321)
!1328 = !DILocation(line: 363, column: 3, scope: !1321)
!1329 = !DILocation(line: 364, column: 1, scope: !1321)
!1330 = distinct !DISubprogram(name: "__ubsan_handle_implicit_conversion", scope: !38, file: !38, line: 404, type: !1331, scopeLine: 406, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1331 = !DISubroutineType(types: !1332)
!1332 = !{null, !1333, !796, !796}
!1333 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1334, size: 64)
!1334 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ImplicitConversionData", file: !317, line: 79, size: 320, flags: DIFlagTypePassByValue | DIFlagNonTrivial, elements: !1335, identifier: "_ZTS22ImplicitConversionData")
!1335 = !{!1336, !1337, !1338, !1339}
!1336 = !DIDerivedType(tag: DW_TAG_member, name: "Loc", scope: !1334, file: !317, line: 80, baseType: !791, size: 128)
!1337 = !DIDerivedType(tag: DW_TAG_member, name: "FromType", scope: !1334, file: !317, line: 81, baseType: !793, size: 64, offset: 128)
!1338 = !DIDerivedType(tag: DW_TAG_member, name: "ToType", scope: !1334, file: !317, line: 82, baseType: !793, size: 64, offset: 192)
!1339 = !DIDerivedType(tag: DW_TAG_member, name: "Kind", scope: !1334, file: !317, line: 83, baseType: !779, size: 8, offset: 256)
!1340 = !DILocalVariable(name: "Data", arg: 1, scope: !1330, file: !38, line: 404, type: !1333)
!1341 = !DILocation(line: 404, column: 76, scope: !1330)
!1342 = !DILocalVariable(name: "Src", arg: 2, scope: !1330, file: !38, line: 405, type: !796)
!1343 = !DILocation(line: 405, column: 64, scope: !1330)
!1344 = !DILocalVariable(name: "Dst", arg: 3, scope: !1330, file: !38, line: 406, type: !796)
!1345 = !DILocation(line: 406, column: 64, scope: !1330)
!1346 = !DILocation(line: 407, column: 28, scope: !1330)
!1347 = !DILocation(line: 407, column: 34, scope: !1330)
!1348 = !DILocation(line: 407, column: 39, scope: !1330)
!1349 = !DILocation(line: 407, column: 3, scope: !1330)
!1350 = !DILocation(line: 408, column: 1, scope: !1330)
!1351 = distinct !DISubprogram(name: "handleImplicitConversion", linkageName: "_ZN7__ubsanL24handleImplicitConversionEP22ImplicitConversionDatamm", scope: !224, file: !38, line: 366, type: !1331, scopeLine: 367, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1352 = !DILocalVariable(name: "Data", arg: 1, scope: !1351, file: !38, line: 366, type: !1333)
!1353 = !DILocation(line: 366, column: 62, scope: !1351)
!1354 = !DILocalVariable(arg: 2, scope: !1351, file: !38, line: 367, type: !796)
!1355 = !DILocation(line: 367, column: 57, scope: !1351)
!1356 = !DILocalVariable(arg: 3, scope: !1351, file: !38, line: 367, type: !796)
!1357 = !DILocation(line: 367, column: 78, scope: !1351)
!1358 = !DILocalVariable(name: "ET", scope: !1351, file: !38, line: 368, type: !256)
!1359 = !DILocation(line: 368, column: 13, scope: !1351)
!1360 = !DILocalVariable(name: "SrcTy", scope: !1351, file: !38, line: 370, type: !793)
!1361 = !DILocation(line: 370, column: 25, scope: !1351)
!1362 = !DILocation(line: 370, column: 33, scope: !1351)
!1363 = !DILocation(line: 370, column: 39, scope: !1351)
!1364 = !DILocalVariable(name: "DstTy", scope: !1351, file: !38, line: 371, type: !793)
!1365 = !DILocation(line: 371, column: 25, scope: !1351)
!1366 = !DILocation(line: 371, column: 33, scope: !1351)
!1367 = !DILocation(line: 371, column: 39, scope: !1351)
!1368 = !DILocalVariable(name: "SrcSigned", scope: !1351, file: !38, line: 373, type: !248)
!1369 = !DILocation(line: 373, column: 8, scope: !1351)
!1370 = !DILocation(line: 373, column: 20, scope: !1351)
!1371 = !DILocation(line: 373, column: 26, scope: !1351)
!1372 = !DILocalVariable(name: "DstSigned", scope: !1351, file: !38, line: 374, type: !248)
!1373 = !DILocation(line: 374, column: 8, scope: !1351)
!1374 = !DILocation(line: 374, column: 20, scope: !1351)
!1375 = !DILocation(line: 374, column: 26, scope: !1351)
!1376 = !DILocation(line: 376, column: 11, scope: !1351)
!1377 = !DILocation(line: 376, column: 17, scope: !1351)
!1378 = !DILocation(line: 376, column: 3, scope: !1351)
!1379 = !DILocation(line: 381, column: 10, scope: !1380)
!1380 = distinct !DILexicalBlock(scope: !1381, file: !38, line: 381, column: 9)
!1381 = distinct !DILexicalBlock(scope: !1382, file: !38, line: 377, column: 32)
!1382 = distinct !DILexicalBlock(scope: !1351, file: !38, line: 376, column: 23)
!1383 = !DILocation(line: 381, column: 20, scope: !1380)
!1384 = !DILocation(line: 381, column: 24, scope: !1380)
!1385 = !DILocation(line: 381, column: 9, scope: !1381)
!1386 = !DILocation(line: 382, column: 10, scope: !1387)
!1387 = distinct !DILexicalBlock(scope: !1380, file: !38, line: 381, column: 35)
!1388 = !DILocation(line: 383, column: 5, scope: !1387)
!1389 = !DILocation(line: 384, column: 10, scope: !1390)
!1390 = distinct !DILexicalBlock(scope: !1380, file: !38, line: 383, column: 12)
!1391 = !DILocation(line: 389, column: 8, scope: !1382)
!1392 = !DILocation(line: 390, column: 5, scope: !1382)
!1393 = !DILocation(line: 392, column: 8, scope: !1382)
!1394 = !DILocation(line: 393, column: 5, scope: !1382)
!1395 = !DILocation(line: 395, column: 8, scope: !1382)
!1396 = !DILocation(line: 396, column: 5, scope: !1382)
!1397 = !DILocation(line: 398, column: 8, scope: !1382)
!1398 = !DILocation(line: 399, column: 5, scope: !1382)
!1399 = !DILocation(line: 401, column: 21, scope: !1351)
!1400 = !DILocation(line: 401, column: 3, scope: !1351)
!1401 = distinct !DISubprogram(name: "__ubsan_handle_implicit_conversion_abort", scope: !38, file: !38, line: 411, type: !1331, scopeLine: 412, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1402 = !DILocalVariable(name: "Data", arg: 1, scope: !1401, file: !38, line: 411, type: !1333)
!1403 = !DILocation(line: 411, column: 66, scope: !1401)
!1404 = !DILocalVariable(name: "Src", arg: 2, scope: !1401, file: !38, line: 412, type: !796)
!1405 = !DILocation(line: 412, column: 54, scope: !1401)
!1406 = !DILocalVariable(name: "Dst", arg: 3, scope: !1401, file: !38, line: 412, type: !796)
!1407 = !DILocation(line: 412, column: 71, scope: !1401)
!1408 = !DILocation(line: 413, column: 28, scope: !1401)
!1409 = !DILocation(line: 413, column: 34, scope: !1401)
!1410 = !DILocation(line: 413, column: 39, scope: !1401)
!1411 = !DILocation(line: 413, column: 3, scope: !1401)
!1412 = !DILocation(line: 414, column: 1, scope: !1401)
!1413 = distinct !DISubprogram(name: "__ubsan_handle_invalid_builtin", scope: !38, file: !38, line: 421, type: !1414, scopeLine: 421, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1414 = !DISubroutineType(types: !1415)
!1415 = !{null, !1416}
!1416 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1417, size: 64)
!1417 = !DICompositeType(tag: DW_TAG_structure_type, name: "InvalidBuiltinData", file: !317, line: 86, size: 192, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS18InvalidBuiltinData")
!1418 = !DILocalVariable(name: "Data", arg: 1, scope: !1413, file: !38, line: 421, type: !1416)
!1419 = !DILocation(line: 421, column: 68, scope: !1413)
!1420 = !DILocation(line: 422, column: 24, scope: !1413)
!1421 = !DILocation(line: 422, column: 3, scope: !1413)
!1422 = !DILocation(line: 423, column: 1, scope: !1413)
!1423 = distinct !DISubprogram(name: "handleInvalidBuiltin", linkageName: "_ZN7__ubsanL20handleInvalidBuiltinEP18InvalidBuiltinData", scope: !224, file: !38, line: 416, type: !1414, scopeLine: 416, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1424 = !DILocalVariable(arg: 1, scope: !1423, file: !38, line: 416, type: !1416)
!1425 = !DILocation(line: 416, column: 63, scope: !1423)
!1426 = !DILocalVariable(name: "ET", scope: !1423, file: !38, line: 417, type: !256)
!1427 = !DILocation(line: 417, column: 13, scope: !1423)
!1428 = !DILocation(line: 418, column: 21, scope: !1423)
!1429 = !DILocation(line: 418, column: 3, scope: !1423)
!1430 = distinct !DISubprogram(name: "__ubsan_handle_invalid_builtin_abort", scope: !38, file: !38, line: 425, type: !1414, scopeLine: 425, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1431 = !DILocalVariable(name: "Data", arg: 1, scope: !1430, file: !38, line: 425, type: !1416)
!1432 = !DILocation(line: 425, column: 74, scope: !1430)
!1433 = !DILocation(line: 426, column: 24, scope: !1430)
!1434 = !DILocation(line: 426, column: 3, scope: !1430)
!1435 = !DILocation(line: 427, column: 1, scope: !1430)
!1436 = distinct !DISubprogram(name: "__ubsan_handle_nonnull_return_v1", scope: !38, file: !38, line: 436, type: !1437, scopeLine: 437, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1437 = !DISubroutineType(types: !1438)
!1438 = !{null, !1439, !1441}
!1439 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1440, size: 64)
!1440 = !DICompositeType(tag: DW_TAG_structure_type, name: "NonNullReturnData", file: !317, line: 91, size: 128, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS17NonNullReturnData")
!1441 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !791, size: 64)
!1442 = !DILocalVariable(name: "Data", arg: 1, scope: !1436, file: !38, line: 436, type: !1439)
!1443 = !DILocation(line: 436, column: 69, scope: !1436)
!1444 = !DILocalVariable(name: "LocPtr", arg: 2, scope: !1436, file: !38, line: 437, type: !1441)
!1445 = !DILocation(line: 437, column: 66, scope: !1436)
!1446 = !DILocation(line: 438, column: 23, scope: !1436)
!1447 = !DILocation(line: 438, column: 29, scope: !1436)
!1448 = !DILocation(line: 438, column: 3, scope: !1436)
!1449 = !DILocation(line: 439, column: 1, scope: !1436)
!1450 = distinct !DISubprogram(name: "handleNonNullReturn", linkageName: "_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb", scope: !224, file: !38, line: 429, type: !1451, scopeLine: 430, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1451 = !DISubroutineType(types: !1452)
!1452 = !{null, !1439, !1441, !248}
!1453 = !DILocalVariable(arg: 1, scope: !1450, file: !38, line: 429, type: !1439)
!1454 = !DILocation(line: 429, column: 61, scope: !1450)
!1455 = !DILocalVariable(arg: 2, scope: !1450, file: !38, line: 430, type: !1441)
!1456 = !DILocation(line: 430, column: 60, scope: !1450)
!1457 = !DILocalVariable(name: "IsAttr", arg: 3, scope: !1450, file: !38, line: 430, type: !248)
!1458 = !DILocation(line: 430, column: 67, scope: !1450)
!1459 = !DILocalVariable(name: "ET", scope: !1450, file: !38, line: 431, type: !256)
!1460 = !DILocation(line: 431, column: 13, scope: !1450)
!1461 = !DILocation(line: 431, column: 18, scope: !1450)
!1462 = !DILocation(line: 433, column: 21, scope: !1450)
!1463 = !DILocation(line: 433, column: 3, scope: !1450)
!1464 = distinct !DISubprogram(name: "__ubsan_handle_nonnull_return_v1_abort", scope: !38, file: !38, line: 441, type: !1437, scopeLine: 442, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1465 = !DILocalVariable(name: "Data", arg: 1, scope: !1464, file: !38, line: 441, type: !1439)
!1466 = !DILocation(line: 441, column: 75, scope: !1464)
!1467 = !DILocalVariable(name: "LocPtr", arg: 2, scope: !1464, file: !38, line: 442, type: !1441)
!1468 = !DILocation(line: 442, column: 72, scope: !1464)
!1469 = !DILocation(line: 443, column: 23, scope: !1464)
!1470 = !DILocation(line: 443, column: 29, scope: !1464)
!1471 = !DILocation(line: 443, column: 3, scope: !1464)
!1472 = !DILocation(line: 444, column: 1, scope: !1464)
!1473 = distinct !DISubprogram(name: "__ubsan_handle_nullability_return_v1", scope: !38, file: !38, line: 446, type: !1437, scopeLine: 447, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1474 = !DILocalVariable(name: "Data", arg: 1, scope: !1473, file: !38, line: 446, type: !1439)
!1475 = !DILocation(line: 446, column: 73, scope: !1473)
!1476 = !DILocalVariable(name: "LocPtr", arg: 2, scope: !1473, file: !38, line: 447, type: !1441)
!1477 = !DILocation(line: 447, column: 70, scope: !1473)
!1478 = !DILocation(line: 448, column: 23, scope: !1473)
!1479 = !DILocation(line: 448, column: 29, scope: !1473)
!1480 = !DILocation(line: 448, column: 3, scope: !1473)
!1481 = !DILocation(line: 449, column: 1, scope: !1473)
!1482 = distinct !DISubprogram(name: "__ubsan_handle_nullability_return_v1_abort", scope: !38, file: !38, line: 452, type: !1437, scopeLine: 453, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1483 = !DILocalVariable(name: "Data", arg: 1, scope: !1482, file: !38, line: 452, type: !1439)
!1484 = !DILocation(line: 452, column: 63, scope: !1482)
!1485 = !DILocalVariable(name: "LocPtr", arg: 2, scope: !1482, file: !38, line: 453, type: !1441)
!1486 = !DILocation(line: 453, column: 60, scope: !1482)
!1487 = !DILocation(line: 454, column: 23, scope: !1482)
!1488 = !DILocation(line: 454, column: 29, scope: !1482)
!1489 = !DILocation(line: 454, column: 3, scope: !1482)
!1490 = !DILocation(line: 455, column: 1, scope: !1482)
!1491 = distinct !DISubprogram(name: "__ubsan_handle_nonnull_arg", scope: !38, file: !38, line: 463, type: !1492, scopeLine: 463, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1492 = !DISubroutineType(types: !1493)
!1493 = !{null, !1494}
!1494 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1495, size: 64)
!1495 = !DICompositeType(tag: DW_TAG_structure_type, name: "NonNullArgData", file: !317, line: 95, size: 320, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS14NonNullArgData")
!1496 = !DILocalVariable(name: "Data", arg: 1, scope: !1491, file: !38, line: 463, type: !1494)
!1497 = !DILocation(line: 463, column: 60, scope: !1491)
!1498 = !DILocation(line: 464, column: 20, scope: !1491)
!1499 = !DILocation(line: 464, column: 3, scope: !1491)
!1500 = !DILocation(line: 465, column: 1, scope: !1491)
!1501 = distinct !DISubprogram(name: "handleNonNullArg", linkageName: "_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab", scope: !224, file: !38, line: 457, type: !1502, scopeLine: 457, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1502 = !DISubroutineType(types: !1503)
!1503 = !{null, !1494, !248}
!1504 = !DILocalVariable(arg: 1, scope: !1501, file: !38, line: 457, type: !1494)
!1505 = !DILocation(line: 457, column: 55, scope: !1501)
!1506 = !DILocalVariable(name: "IsAttr", arg: 2, scope: !1501, file: !38, line: 457, type: !248)
!1507 = !DILocation(line: 457, column: 62, scope: !1501)
!1508 = !DILocalVariable(name: "ET", scope: !1501, file: !38, line: 458, type: !256)
!1509 = !DILocation(line: 458, column: 13, scope: !1501)
!1510 = !DILocation(line: 458, column: 18, scope: !1501)
!1511 = !DILocation(line: 460, column: 21, scope: !1501)
!1512 = !DILocation(line: 460, column: 3, scope: !1501)
!1513 = distinct !DISubprogram(name: "__ubsan_handle_nonnull_arg_abort", scope: !38, file: !38, line: 467, type: !1492, scopeLine: 467, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1514 = !DILocalVariable(name: "Data", arg: 1, scope: !1513, file: !38, line: 467, type: !1494)
!1515 = !DILocation(line: 467, column: 66, scope: !1513)
!1516 = !DILocation(line: 468, column: 20, scope: !1513)
!1517 = !DILocation(line: 468, column: 3, scope: !1513)
!1518 = !DILocation(line: 469, column: 1, scope: !1513)
!1519 = distinct !DISubprogram(name: "__ubsan_handle_nullability_arg", scope: !38, file: !38, line: 471, type: !1492, scopeLine: 471, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1520 = !DILocalVariable(name: "Data", arg: 1, scope: !1519, file: !38, line: 471, type: !1494)
!1521 = !DILocation(line: 471, column: 64, scope: !1519)
!1522 = !DILocation(line: 472, column: 20, scope: !1519)
!1523 = !DILocation(line: 472, column: 3, scope: !1519)
!1524 = !DILocation(line: 473, column: 1, scope: !1519)
!1525 = distinct !DISubprogram(name: "__ubsan_handle_nullability_arg_abort", scope: !38, file: !38, line: 475, type: !1492, scopeLine: 475, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1526 = !DILocalVariable(name: "Data", arg: 1, scope: !1525, file: !38, line: 475, type: !1494)
!1527 = !DILocation(line: 475, column: 70, scope: !1525)
!1528 = !DILocation(line: 477, column: 20, scope: !1525)
!1529 = !DILocation(line: 477, column: 3, scope: !1525)
!1530 = !DILocation(line: 478, column: 1, scope: !1525)
!1531 = distinct !DISubprogram(name: "__ubsan_handle_pointer_overflow", scope: !38, file: !38, line: 494, type: !1532, scopeLine: 496, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1532 = !DISubroutineType(types: !1533)
!1533 = !{null, !1534, !796, !796}
!1534 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1535, size: 64)
!1535 = !DICompositeType(tag: DW_TAG_structure_type, name: "PointerOverflowData", file: !317, line: 101, size: 128, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS19PointerOverflowData")
!1536 = !DILocalVariable(name: "Data", arg: 1, scope: !1531, file: !38, line: 494, type: !1534)
!1537 = !DILocation(line: 494, column: 70, scope: !1531)
!1538 = !DILocalVariable(name: "Base", arg: 2, scope: !1531, file: !38, line: 495, type: !796)
!1539 = !DILocation(line: 495, column: 61, scope: !1531)
!1540 = !DILocalVariable(name: "Result", arg: 3, scope: !1531, file: !38, line: 496, type: !796)
!1541 = !DILocation(line: 496, column: 61, scope: !1531)
!1542 = !DILocation(line: 498, column: 29, scope: !1531)
!1543 = !DILocation(line: 498, column: 35, scope: !1531)
!1544 = !DILocation(line: 498, column: 41, scope: !1531)
!1545 = !DILocation(line: 498, column: 3, scope: !1531)
!1546 = !DILocation(line: 499, column: 1, scope: !1531)
!1547 = distinct !DISubprogram(name: "handlePointerOverflowImpl", linkageName: "_ZN7__ubsanL25handlePointerOverflowImplEP19PointerOverflowDatamm", scope: !224, file: !38, line: 480, type: !1532, scopeLine: 481, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1548 = !DILocalVariable(arg: 1, scope: !1547, file: !38, line: 480, type: !1534)
!1549 = !DILocation(line: 480, column: 69, scope: !1547)
!1550 = !DILocalVariable(name: "Base", arg: 2, scope: !1547, file: !38, line: 481, type: !796)
!1551 = !DILocation(line: 481, column: 51, scope: !1547)
!1552 = !DILocalVariable(name: "Result", arg: 3, scope: !1547, file: !38, line: 481, type: !796)
!1553 = !DILocation(line: 481, column: 69, scope: !1547)
!1554 = !DILocalVariable(name: "ET", scope: !1547, file: !38, line: 482, type: !256)
!1555 = !DILocation(line: 482, column: 13, scope: !1547)
!1556 = !DILocation(line: 483, column: 7, scope: !1557)
!1557 = distinct !DILexicalBlock(scope: !1547, file: !38, line: 483, column: 7)
!1558 = !DILocation(line: 483, column: 12, scope: !1557)
!1559 = !DILocation(line: 483, column: 17, scope: !1557)
!1560 = !DILocation(line: 484, column: 8, scope: !1557)
!1561 = !DILocation(line: 484, column: 5, scope: !1557)
!1562 = !DILocation(line: 485, column: 12, scope: !1563)
!1563 = distinct !DILexicalBlock(scope: !1557, file: !38, line: 485, column: 12)
!1564 = !DILocation(line: 485, column: 17, scope: !1563)
!1565 = !DILocation(line: 485, column: 22, scope: !1563)
!1566 = !DILocation(line: 486, column: 8, scope: !1563)
!1567 = !DILocation(line: 486, column: 5, scope: !1563)
!1568 = !DILocation(line: 487, column: 12, scope: !1569)
!1569 = distinct !DILexicalBlock(scope: !1563, file: !38, line: 487, column: 12)
!1570 = !DILocation(line: 487, column: 17, scope: !1569)
!1571 = !DILocation(line: 487, column: 22, scope: !1569)
!1572 = !DILocation(line: 488, column: 8, scope: !1569)
!1573 = !DILocation(line: 488, column: 5, scope: !1569)
!1574 = !DILocation(line: 490, column: 8, scope: !1569)
!1575 = !DILocation(line: 491, column: 21, scope: !1547)
!1576 = !DILocation(line: 491, column: 3, scope: !1547)
!1577 = distinct !DISubprogram(name: "__ubsan_handle_pointer_overflow_abort", scope: !38, file: !38, line: 501, type: !1532, scopeLine: 503, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1578 = !DILocalVariable(name: "Data", arg: 1, scope: !1577, file: !38, line: 501, type: !1534)
!1579 = !DILocation(line: 501, column: 76, scope: !1577)
!1580 = !DILocalVariable(name: "Base", arg: 2, scope: !1577, file: !38, line: 502, type: !796)
!1581 = !DILocation(line: 502, column: 67, scope: !1577)
!1582 = !DILocalVariable(name: "Result", arg: 3, scope: !1577, file: !38, line: 503, type: !796)
!1583 = !DILocation(line: 503, column: 67, scope: !1577)
!1584 = !DILocation(line: 505, column: 29, scope: !1577)
!1585 = !DILocation(line: 505, column: 35, scope: !1577)
!1586 = !DILocation(line: 505, column: 41, scope: !1577)
!1587 = !DILocation(line: 505, column: 3, scope: !1577)
!1588 = !DILocation(line: 506, column: 1, scope: !1577)
!1589 = distinct !DISubprogram(name: "__ubsan_handle_function_type_mismatch", scope: !38, file: !38, line: 516, type: !1590, scopeLine: 517, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1590 = !DISubroutineType(types: !1591)
!1591 = !{null, !1592, !796}
!1592 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1593, size: 64)
!1593 = !DICompositeType(tag: DW_TAG_structure_type, name: "FunctionTypeMismatchData", file: !317, line: 106, size: 192, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS24FunctionTypeMismatchData")
!1594 = !DILocalVariable(name: "Data", arg: 1, scope: !1589, file: !38, line: 516, type: !1592)
!1595 = !DILocation(line: 516, column: 65, scope: !1589)
!1596 = !DILocalVariable(name: "Function", arg: 2, scope: !1589, file: !38, line: 517, type: !796)
!1597 = !DILocation(line: 517, column: 51, scope: !1589)
!1598 = !DILocation(line: 518, column: 30, scope: !1589)
!1599 = !DILocation(line: 518, column: 36, scope: !1589)
!1600 = !DILocation(line: 518, column: 3, scope: !1589)
!1601 = !DILocation(line: 519, column: 1, scope: !1589)
!1602 = distinct !DISubprogram(name: "handleFunctionTypeMismatch", linkageName: "_ZN7__ubsanL26handleFunctionTypeMismatchEP24FunctionTypeMismatchDatam", scope: !224, file: !38, line: 509, type: !1590, scopeLine: 510, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1603 = !DILocalVariable(arg: 1, scope: !1602, file: !38, line: 509, type: !1592)
!1604 = !DILocation(line: 509, column: 75, scope: !1602)
!1605 = !DILocalVariable(arg: 2, scope: !1602, file: !38, line: 510, type: !796)
!1606 = !DILocation(line: 510, column: 64, scope: !1602)
!1607 = !DILocalVariable(name: "ET", scope: !1602, file: !38, line: 511, type: !256)
!1608 = !DILocation(line: 511, column: 13, scope: !1602)
!1609 = !DILocation(line: 512, column: 21, scope: !1602)
!1610 = !DILocation(line: 512, column: 3, scope: !1602)
!1611 = distinct !DISubprogram(name: "__ubsan_handle_function_type_mismatch_abort", scope: !38, file: !38, line: 522, type: !1590, scopeLine: 523, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1612 = !DILocalVariable(name: "Data", arg: 1, scope: !1611, file: !38, line: 522, type: !1592)
!1613 = !DILocation(line: 522, column: 71, scope: !1611)
!1614 = !DILocalVariable(name: "Function", arg: 2, scope: !1611, file: !38, line: 523, type: !796)
!1615 = !DILocation(line: 523, column: 57, scope: !1611)
!1616 = !DILocation(line: 524, column: 30, scope: !1611)
!1617 = !DILocation(line: 524, column: 36, scope: !1611)
!1618 = !DILocation(line: 524, column: 3, scope: !1611)
!1619 = !DILocation(line: 525, column: 1, scope: !1611)
!1620 = distinct !DISubprogram(name: "klee_overshift_check", scope: !201, file: !201, line: 20, type: !1621, scopeLine: 20, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !318, retainedNodes: !334)
!1621 = !DISubroutineType(types: !1622)
!1622 = !{null, !1623, !1623}
!1623 = !DIBasicType(name: "unsigned long long", size: 64, encoding: DW_ATE_unsigned)
!1624 = !DILocalVariable(name: "bitWidth", arg: 1, scope: !1620, file: !201, line: 20, type: !1623)
!1625 = !DILocation(line: 20, column: 46, scope: !1620)
!1626 = !DILocalVariable(name: "shift", arg: 2, scope: !1620, file: !201, line: 20, type: !1623)
!1627 = !DILocation(line: 20, column: 75, scope: !1620)
!1628 = !DILocation(line: 21, column: 7, scope: !1629)
!1629 = distinct !DILexicalBlock(scope: !1620, file: !201, line: 21, column: 7)
!1630 = !DILocation(line: 21, column: 16, scope: !1629)
!1631 = !DILocation(line: 21, column: 13, scope: !1629)
!1632 = !DILocation(line: 21, column: 7, scope: !1620)
!1633 = !DILocation(line: 27, column: 5, scope: !1634)
!1634 = distinct !DILexicalBlock(scope: !1629, file: !201, line: 21, column: 26)
!1635 = !DILocation(line: 29, column: 1, scope: !1620)
