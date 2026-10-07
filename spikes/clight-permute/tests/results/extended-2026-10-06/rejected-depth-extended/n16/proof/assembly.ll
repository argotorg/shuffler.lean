; ModuleID = '/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo/spikes/clight-permute/build/equiv-alive2/rejected-depth-extended/n16/linked.bc'
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
@0 = private unnamed_addr constant { i16, i16, [19 x i8] } { i16 -1, i16 0, [19 x i8] c"'unsigned int[35]'\00" }
@1 = private unnamed_addr constant { i16, i16, [15 x i8] } { i16 0, i16 10, [15 x i8] c"'unsigned int'\00" }
@2 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 25, i32 18 }, ptr @0, ptr @1 }
@3 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 27, i32 22 }, ptr @0, ptr @1 }
@4 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 27, i32 34 }, ptr @0, ptr @1 }
@5 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 28, i32 26 }, ptr @0, ptr @1 }
@6 = private unnamed_addr constant { i16, i16, [19 x i8] } { i16 -1, i16 0, [19 x i8] c"'unsigned int[16]'\00" }
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
  %1 = alloca [35 x i32], align 16
  %2 = alloca [16 x i32], align 16
  %3 = alloca [16 x i32], align 16
  %4 = alloca [16 x i32], align 16
  %5 = alloca [16 x i32], align 16
  %6 = alloca [32 x i32], align 16
  %7 = alloca [3 x i32], align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
    #dbg_declare(ptr %1, !640, !DIExpression(), !642)
    #dbg_declare(ptr %2, !643, !DIExpression(), !645)
    #dbg_declare(ptr %3, !646, !DIExpression(), !647)
    #dbg_declare(ptr %4, !648, !DIExpression(), !649)
    #dbg_declare(ptr %5, !650, !DIExpression(), !651)
    #dbg_declare(ptr %6, !652, !DIExpression(), !656)
    #dbg_declare(ptr %7, !657, !DIExpression(), !661)
  %15 = getelementptr inbounds [35 x i32], ptr %1, i64 0, i64 0, !dbg !662
  call void @klee_make_symbolic(ptr noundef %15, i64 noundef 140, ptr noundef @.str), !dbg !663
    #dbg_declare(ptr %8, !664, !DIExpression(), !665)
  store i32 1, ptr %8, align 4, !dbg !665
    #dbg_declare(ptr %9, !666, !DIExpression(), !668)
  store i32 0, ptr %9, align 4, !dbg !668
  br label %16, !dbg !669

16:                                               ; preds = %146, %0
  %17 = load i32, ptr %9, align 4, !dbg !670
  %18 = icmp ult i32 %17, 16, !dbg !672
  br i1 %18, label %19, label %149, !dbg !673

19:                                               ; preds = %16
  %20 = load i32, ptr %9, align 4, !dbg !674
  %21 = zext i32 %20 to i64, !dbg !676, !nosanitize !334
  %22 = icmp ult i64 %21, 35, !dbg !676, !nosanitize !334
  br i1 %22, label %25, label %23, !dbg !676, !prof !677, !nosanitize !334

23:                                               ; preds = %19
  %24 = zext i32 %20 to i64, !dbg !676, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @2, i64 %24) #7, !dbg !676, !nosanitize !334
  unreachable, !dbg !676, !nosanitize !334

25:                                               ; preds = %19
  %26 = zext i32 %20 to i64, !dbg !676
  %27 = mul i64 %26, 4, !dbg !676
  %28 = add i64 0, %27, !dbg !676
  %29 = getelementptr [35 x i32], ptr %1, i64 0, i64 %26, !dbg !676
  %30 = sub i64 144, %28, !dbg !676
  %31 = icmp ult i64 144, %28, !dbg !676
  %32 = icmp ult i64 %30, 4, !dbg !676
  %33 = or i1 %31, %32, !dbg !676
  br i1 %33, label %308, label %34

34:                                               ; preds = %25
  %35 = load i32, ptr %29, align 4, !dbg !676
  %36 = icmp ult i32 %35, 16, !dbg !678
  %37 = zext i1 %36 to i32, !dbg !678
  %38 = load i32, ptr %8, align 4, !dbg !679
  %39 = and i32 %38, %37, !dbg !679
  store i32 %39, ptr %8, align 4, !dbg !679
    #dbg_declare(ptr %10, !680, !DIExpression(), !682)
  store i32 0, ptr %10, align 4, !dbg !682
  br label %40, !dbg !683

40:                                               ; preds = %75, %34
  %41 = load i32, ptr %10, align 4, !dbg !684
  %42 = load i32, ptr %9, align 4, !dbg !686
  %43 = icmp ult i32 %41, %42, !dbg !687
  br i1 %43, label %44, label %83, !dbg !688

44:                                               ; preds = %40
  %45 = load i32, ptr %9, align 4, !dbg !689
  %46 = zext i32 %45 to i64, !dbg !690, !nosanitize !334
  %47 = icmp ult i64 %46, 35, !dbg !690, !nosanitize !334
  br i1 %47, label %50, label %48, !dbg !690, !prof !677, !nosanitize !334

48:                                               ; preds = %44
  %49 = zext i32 %45 to i64, !dbg !690, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @3, i64 %49) #7, !dbg !690, !nosanitize !334
  unreachable, !dbg !690, !nosanitize !334

50:                                               ; preds = %44
  %51 = zext i32 %45 to i64, !dbg !690
  %52 = mul i64 %51, 4, !dbg !690
  %53 = add i64 0, %52, !dbg !690
  %54 = getelementptr [35 x i32], ptr %1, i64 0, i64 %51, !dbg !690
  %55 = sub i64 144, %53, !dbg !690
  %56 = icmp ult i64 144, %53, !dbg !690
  %57 = icmp ult i64 %55, 4, !dbg !690
  %58 = or i1 %56, %57, !dbg !690
  br i1 %58, label %309, label %59

59:                                               ; preds = %50
  %60 = load i32, ptr %54, align 4, !dbg !690
  %61 = load i32, ptr %10, align 4, !dbg !691
  %62 = zext i32 %61 to i64, !dbg !692, !nosanitize !334
  %63 = icmp ult i64 %62, 35, !dbg !692, !nosanitize !334
  br i1 %63, label %66, label %64, !dbg !692, !prof !677, !nosanitize !334

64:                                               ; preds = %59
  %65 = zext i32 %61 to i64, !dbg !692, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @4, i64 %65) #7, !dbg !692, !nosanitize !334
  unreachable, !dbg !692, !nosanitize !334

66:                                               ; preds = %59
  %67 = zext i32 %61 to i64, !dbg !692
  %68 = mul i64 %67, 4, !dbg !692
  %69 = add i64 0, %68, !dbg !692
  %70 = getelementptr [35 x i32], ptr %1, i64 0, i64 %67, !dbg !692
  %71 = sub i64 144, %69, !dbg !692
  %72 = icmp ult i64 144, %69, !dbg !692
  %73 = icmp ult i64 %71, 4, !dbg !692
  %74 = or i1 %72, %73, !dbg !692
  br i1 %74, label %310, label %75

75:                                               ; preds = %66
  %76 = load i32, ptr %70, align 4, !dbg !692
  %77 = icmp ne i32 %60, %76, !dbg !693
  %78 = zext i1 %77 to i32, !dbg !693
  %79 = load i32, ptr %8, align 4, !dbg !694
  %80 = and i32 %79, %78, !dbg !694
  store i32 %80, ptr %8, align 4, !dbg !694
  %81 = load i32, ptr %10, align 4, !dbg !695
  %82 = add i32 %81, 1, !dbg !695
  store i32 %82, ptr %10, align 4, !dbg !695
  br label %40, !dbg !696, !llvm.loop !697

83:                                               ; preds = %40
  %84 = load i32, ptr %9, align 4, !dbg !700
  %85 = zext i32 %84 to i64, !dbg !701, !nosanitize !334
  %86 = icmp ult i64 %85, 35, !dbg !701, !nosanitize !334
  br i1 %86, label %89, label %87, !dbg !701, !prof !677, !nosanitize !334

87:                                               ; preds = %83
  %88 = zext i32 %84 to i64, !dbg !701, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @5, i64 %88) #7, !dbg !701, !nosanitize !334
  unreachable, !dbg !701, !nosanitize !334

89:                                               ; preds = %83
  %90 = zext i32 %84 to i64, !dbg !701
  %91 = mul i64 %90, 4, !dbg !701
  %92 = add i64 0, %91, !dbg !701
  %93 = getelementptr [35 x i32], ptr %1, i64 0, i64 %90, !dbg !701
  %94 = sub i64 144, %92, !dbg !701
  %95 = icmp ult i64 144, %92, !dbg !701
  %96 = icmp ult i64 %94, 4, !dbg !701
  %97 = or i1 %95, %96, !dbg !701
  br i1 %97, label %311, label %98

98:                                               ; preds = %89
  %99 = load i32, ptr %93, align 4, !dbg !701
  %100 = load i32, ptr %9, align 4, !dbg !702
  %101 = zext i32 %100 to i64, !dbg !703, !nosanitize !334
  %102 = icmp ult i64 %101, 16, !dbg !703, !nosanitize !334
  br i1 %102, label %105, label %103, !dbg !703, !prof !677, !nosanitize !334

103:                                              ; preds = %98
  %104 = zext i32 %100 to i64, !dbg !703, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @7, i64 %104) #7, !dbg !703, !nosanitize !334
  unreachable, !dbg !703, !nosanitize !334

105:                                              ; preds = %98
  %106 = zext i32 %100 to i64, !dbg !703
  %107 = mul i64 %106, 4, !dbg !703
  %108 = add i64 0, %107, !dbg !703
  %109 = getelementptr [16 x i32], ptr %3, i64 0, i64 %106, !dbg !703
  %110 = sub i64 64, %108, !dbg !703
  %111 = icmp ult i64 64, %108, !dbg !703
  %112 = icmp ult i64 %110, 4, !dbg !703
  %113 = or i1 %111, %112, !dbg !703
  br i1 %113, label %312, label %114

114:                                              ; preds = %105
  store i32 %99, ptr %109, align 4, !dbg !703
  %115 = load i32, ptr %9, align 4, !dbg !704
  %116 = add i32 16, %115, !dbg !705
  %117 = zext i32 %116 to i64, !dbg !706, !nosanitize !334
  %118 = icmp ult i64 %117, 35, !dbg !706, !nosanitize !334
  br i1 %118, label %121, label %119, !dbg !706, !prof !677, !nosanitize !334

119:                                              ; preds = %114
  %120 = zext i32 %116 to i64, !dbg !706, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @8, i64 %120) #7, !dbg !706, !nosanitize !334
  unreachable, !dbg !706, !nosanitize !334

121:                                              ; preds = %114
  %122 = zext i32 %116 to i64, !dbg !706
  %123 = mul i64 %122, 4, !dbg !706
  %124 = add i64 0, %123, !dbg !706
  %125 = getelementptr [35 x i32], ptr %1, i64 0, i64 %122, !dbg !706
  %126 = sub i64 144, %124, !dbg !706
  %127 = icmp ult i64 144, %124, !dbg !706
  %128 = icmp ult i64 %126, 4, !dbg !706
  %129 = or i1 %127, %128, !dbg !706
  br i1 %129, label %313, label %130

130:                                              ; preds = %121
  %131 = load i32, ptr %125, align 4, !dbg !706
  %132 = load i32, ptr %9, align 4, !dbg !707
  %133 = zext i32 %132 to i64, !dbg !708, !nosanitize !334
  %134 = icmp ult i64 %133, 16, !dbg !708, !nosanitize !334
  br i1 %134, label %137, label %135, !dbg !708, !prof !677, !nosanitize !334

135:                                              ; preds = %130
  %136 = zext i32 %132 to i64, !dbg !708, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @9, i64 %136) #7, !dbg !708, !nosanitize !334
  unreachable, !dbg !708, !nosanitize !334

137:                                              ; preds = %130
  %138 = zext i32 %132 to i64, !dbg !708
  %139 = mul i64 %138, 4, !dbg !708
  %140 = add i64 0, %139, !dbg !708
  %141 = getelementptr [16 x i32], ptr %2, i64 0, i64 %138, !dbg !708
  %142 = sub i64 64, %140, !dbg !708
  %143 = icmp ult i64 64, %140, !dbg !708
  %144 = icmp ult i64 %142, 4, !dbg !708
  %145 = or i1 %143, %144, !dbg !708
  br i1 %145, label %314, label %146

146:                                              ; preds = %137
  store i32 %131, ptr %141, align 4, !dbg !708
  %147 = load i32, ptr %9, align 4, !dbg !709
  %148 = add i32 %147, 1, !dbg !709
  store i32 %148, ptr %9, align 4, !dbg !709
  br label %16, !dbg !710, !llvm.loop !711

149:                                              ; preds = %16
  %150 = load i32, ptr %8, align 4, !dbg !713
  %151 = icmp eq i32 %150, 0, !dbg !714
  %152 = zext i1 %151 to i32, !dbg !714
  %153 = sext i32 %152 to i64, !dbg !713
  call void @klee_assume(i64 noundef %153), !dbg !715
    #dbg_declare(ptr %11, !716, !DIExpression(), !718)
  store i32 0, ptr %11, align 4, !dbg !718
  br label %154, !dbg !719

154:                                              ; preds = %189, %149
  %155 = load i32, ptr %11, align 4, !dbg !720
  %156 = icmp ult i32 %155, 3, !dbg !722
  br i1 %156, label %157, label %192, !dbg !723

157:                                              ; preds = %154
  %158 = load i32, ptr %11, align 4, !dbg !724
  %159 = add i32 32, %158, !dbg !725
  %160 = zext i32 %159 to i64, !dbg !726, !nosanitize !334
  %161 = icmp ult i64 %160, 35, !dbg !726, !nosanitize !334
  br i1 %161, label %164, label %162, !dbg !726, !prof !677, !nosanitize !334

162:                                              ; preds = %157
  %163 = zext i32 %159 to i64, !dbg !726, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @10, i64 %163) #7, !dbg !726, !nosanitize !334
  unreachable, !dbg !726, !nosanitize !334

164:                                              ; preds = %157
  %165 = zext i32 %159 to i64, !dbg !726
  %166 = mul i64 %165, 4, !dbg !726
  %167 = add i64 0, %166, !dbg !726
  %168 = getelementptr [35 x i32], ptr %1, i64 0, i64 %165, !dbg !726
  %169 = sub i64 144, %167, !dbg !726
  %170 = icmp ult i64 144, %167, !dbg !726
  %171 = icmp ult i64 %169, 4, !dbg !726
  %172 = or i1 %170, %171, !dbg !726
  br i1 %172, label %315, label %173

173:                                              ; preds = %164
  %174 = load i32, ptr %168, align 4, !dbg !726
  %175 = load i32, ptr %11, align 4, !dbg !727
  %176 = zext i32 %175 to i64, !dbg !728, !nosanitize !334
  %177 = icmp ult i64 %176, 3, !dbg !728, !nosanitize !334
  br i1 %177, label %180, label %178, !dbg !728, !prof !677, !nosanitize !334

178:                                              ; preds = %173
  %179 = zext i32 %175 to i64, !dbg !728, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @12, i64 %179) #7, !dbg !728, !nosanitize !334
  unreachable, !dbg !728, !nosanitize !334

180:                                              ; preds = %173
  %181 = zext i32 %175 to i64, !dbg !728
  %182 = mul i64 %181, 4, !dbg !728
  %183 = add i64 0, %182, !dbg !728
  %184 = getelementptr [3 x i32], ptr %7, i64 0, i64 %181, !dbg !728
  %185 = sub i64 12, %183, !dbg !728
  %186 = icmp ult i64 12, %183, !dbg !728
  %187 = icmp ult i64 %185, 4, !dbg !728
  %188 = or i1 %186, %187, !dbg !728
  br i1 %188, label %316, label %189

189:                                              ; preds = %180
  store i32 %174, ptr %184, align 4, !dbg !728
  %190 = load i32, ptr %11, align 4, !dbg !729
  %191 = add i32 %190, 1, !dbg !729
  store i32 %191, ptr %11, align 4, !dbg !729
  br label %154, !dbg !730, !llvm.loop !731

192:                                              ; preds = %154
    #dbg_declare(ptr %12, !733, !DIExpression(), !734)
  %193 = getelementptr inbounds [16 x i32], ptr %2, i64 0, i64 0, !dbg !735
  %194 = getelementptr inbounds [16 x i32], ptr %3, i64 0, i64 0, !dbg !736
  %195 = getelementptr inbounds [16 x i32], ptr %4, i64 0, i64 0, !dbg !737
  %196 = getelementptr inbounds [16 x i32], ptr %5, i64 0, i64 0, !dbg !738
  %197 = getelementptr inbounds [32 x i32], ptr %6, i64 0, i64 0, !dbg !739
  %198 = getelementptr inbounds [3 x i32], ptr %7, i64 0, i64 0, !dbg !740
  %199 = call i32 @permute(i32 noundef 16, ptr noundef %193, ptr noundef %194, ptr noundef %195, ptr noundef %196, ptr noundef %197, ptr noundef %198), !dbg !741
  store i32 %199, ptr %12, align 4, !dbg !734
  %200 = load i32, ptr %12, align 4, !dbg !742
  %201 = icmp eq i32 %200, 2, !dbg !742
  br i1 %201, label %203, label %202, !dbg !742

202:                                              ; preds = %192
  call void @klee_assert_fail(ptr noundef @.str.1, ptr noundef @.src, i32 noundef 37, ptr noundef @__PRETTY_FUNCTION__.checked_main) #8, !dbg !742
  unreachable, !dbg !742

203:                                              ; preds = %192
    #dbg_declare(ptr %13, !743, !DIExpression(), !745)
  store i32 0, ptr %13, align 4, !dbg !745
  br label %204, !dbg !746

204:                                              ; preds = %278, %203
  %205 = load i32, ptr %13, align 4, !dbg !747
  %206 = icmp ult i32 %205, 16, !dbg !749
  br i1 %206, label %207, label %281, !dbg !750

207:                                              ; preds = %204
  %208 = load i32, ptr %13, align 4, !dbg !751
  %209 = zext i32 %208 to i64, !dbg !751, !nosanitize !334
  %210 = icmp ult i64 %209, 16, !dbg !751, !nosanitize !334
  br i1 %210, label %213, label %211, !dbg !751, !prof !677, !nosanitize !334

211:                                              ; preds = %207
  %212 = zext i32 %208 to i64, !dbg !751, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @13, i64 %212) #7, !dbg !751, !nosanitize !334
  unreachable, !dbg !751, !nosanitize !334

213:                                              ; preds = %207
  %214 = zext i32 %208 to i64, !dbg !751
  %215 = mul i64 %214, 4, !dbg !751
  %216 = add i64 0, %215, !dbg !751
  %217 = getelementptr [16 x i32], ptr %3, i64 0, i64 %214, !dbg !751
  %218 = sub i64 64, %216, !dbg !751
  %219 = icmp ult i64 64, %216, !dbg !751
  %220 = icmp ult i64 %218, 4, !dbg !751
  %221 = or i1 %219, %220, !dbg !751
  br i1 %221, label %317, label %222

222:                                              ; preds = %213
  %223 = load i32, ptr %217, align 4, !dbg !751
  %224 = load i32, ptr %13, align 4, !dbg !751
  %225 = zext i32 %224 to i64, !dbg !751, !nosanitize !334
  %226 = icmp ult i64 %225, 35, !dbg !751, !nosanitize !334
  br i1 %226, label %229, label %227, !dbg !751, !prof !677, !nosanitize !334

227:                                              ; preds = %222
  %228 = zext i32 %224 to i64, !dbg !751, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @14, i64 %228) #7, !dbg !751, !nosanitize !334
  unreachable, !dbg !751, !nosanitize !334

229:                                              ; preds = %222
  %230 = zext i32 %224 to i64, !dbg !751
  %231 = mul i64 %230, 4, !dbg !751
  %232 = add i64 0, %231, !dbg !751
  %233 = getelementptr [35 x i32], ptr %1, i64 0, i64 %230, !dbg !751
  %234 = sub i64 144, %232, !dbg !751
  %235 = icmp ult i64 144, %232, !dbg !751
  %236 = icmp ult i64 %234, 4, !dbg !751
  %237 = or i1 %235, %236, !dbg !751
  br i1 %237, label %318, label %238

238:                                              ; preds = %229
  %239 = load i32, ptr %233, align 4, !dbg !751
  %240 = icmp eq i32 %223, %239, !dbg !751
  br i1 %240, label %242, label %241, !dbg !751

241:                                              ; preds = %238
  call void @klee_assert_fail(ptr noundef @.str.2, ptr noundef @.src, i32 noundef 39, ptr noundef @__PRETTY_FUNCTION__.checked_main) #8, !dbg !751
  unreachable, !dbg !751

242:                                              ; preds = %238
  %243 = load i32, ptr %13, align 4, !dbg !753
  %244 = zext i32 %243 to i64, !dbg !753, !nosanitize !334
  %245 = icmp ult i64 %244, 16, !dbg !753, !nosanitize !334
  br i1 %245, label %248, label %246, !dbg !753, !prof !677, !nosanitize !334

246:                                              ; preds = %242
  %247 = zext i32 %243 to i64, !dbg !753, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @15, i64 %247) #7, !dbg !753, !nosanitize !334
  unreachable, !dbg !753, !nosanitize !334

248:                                              ; preds = %242
  %249 = zext i32 %243 to i64, !dbg !753
  %250 = mul i64 %249, 4, !dbg !753
  %251 = add i64 0, %250, !dbg !753
  %252 = getelementptr [16 x i32], ptr %2, i64 0, i64 %249, !dbg !753
  %253 = sub i64 64, %251, !dbg !753
  %254 = icmp ult i64 64, %251, !dbg !753
  %255 = icmp ult i64 %253, 4, !dbg !753
  %256 = or i1 %254, %255, !dbg !753
  br i1 %256, label %319, label %257

257:                                              ; preds = %248
  %258 = load i32, ptr %252, align 4, !dbg !753
  %259 = load i32, ptr %13, align 4, !dbg !753
  %260 = add i32 16, %259, !dbg !753
  %261 = zext i32 %260 to i64, !dbg !753, !nosanitize !334
  %262 = icmp ult i64 %261, 35, !dbg !753, !nosanitize !334
  br i1 %262, label %265, label %263, !dbg !753, !prof !677, !nosanitize !334

263:                                              ; preds = %257
  %264 = zext i32 %260 to i64, !dbg !753, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @16, i64 %264) #7, !dbg !753, !nosanitize !334
  unreachable, !dbg !753, !nosanitize !334

265:                                              ; preds = %257
  %266 = zext i32 %260 to i64, !dbg !753
  %267 = mul i64 %266, 4, !dbg !753
  %268 = add i64 0, %267, !dbg !753
  %269 = getelementptr [35 x i32], ptr %1, i64 0, i64 %266, !dbg !753
  %270 = sub i64 144, %268, !dbg !753
  %271 = icmp ult i64 144, %268, !dbg !753
  %272 = icmp ult i64 %270, 4, !dbg !753
  %273 = or i1 %271, %272, !dbg !753
  br i1 %273, label %320, label %274

274:                                              ; preds = %265
  %275 = load i32, ptr %269, align 4, !dbg !753
  %276 = icmp eq i32 %258, %275, !dbg !753
  br i1 %276, label %278, label %277, !dbg !753

277:                                              ; preds = %274
  call void @klee_assert_fail(ptr noundef @.str.3, ptr noundef @.src, i32 noundef 40, ptr noundef @__PRETTY_FUNCTION__.checked_main) #8, !dbg !753
  unreachable, !dbg !753

278:                                              ; preds = %274
  %279 = load i32, ptr %13, align 4, !dbg !754
  %280 = add i32 %279, 1, !dbg !754
  store i32 %280, ptr %13, align 4, !dbg !754
  br label %204, !dbg !755, !llvm.loop !756

281:                                              ; preds = %204
    #dbg_declare(ptr %14, !758, !DIExpression(), !760)
  store i32 0, ptr %14, align 4, !dbg !760
  br label %282, !dbg !761

282:                                              ; preds = %304, %281
  %283 = load i32, ptr %14, align 4, !dbg !762
  %284 = icmp ult i32 %283, 3, !dbg !764
  br i1 %284, label %285, label %307, !dbg !765

285:                                              ; preds = %282
  %286 = load i32, ptr %14, align 4, !dbg !766
  %287 = zext i32 %286 to i64, !dbg !766, !nosanitize !334
  %288 = icmp ult i64 %287, 3, !dbg !766, !nosanitize !334
  br i1 %288, label %291, label %289, !dbg !766, !prof !677, !nosanitize !334

289:                                              ; preds = %285
  %290 = zext i32 %286 to i64, !dbg !766, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @17, i64 %290) #7, !dbg !766, !nosanitize !334
  unreachable, !dbg !766, !nosanitize !334

291:                                              ; preds = %285
  %292 = zext i32 %286 to i64, !dbg !766
  %293 = mul i64 %292, 4, !dbg !766
  %294 = add i64 0, %293, !dbg !766
  %295 = getelementptr [3 x i32], ptr %7, i64 0, i64 %292, !dbg !766
  %296 = sub i64 12, %294, !dbg !766
  %297 = icmp ult i64 12, %294, !dbg !766
  %298 = icmp ult i64 %296, 4, !dbg !766
  %299 = or i1 %297, %298, !dbg !766
  br i1 %299, label %321, label %300

300:                                              ; preds = %291
  %301 = load i32, ptr %295, align 4, !dbg !766
  %302 = icmp eq i32 %301, 0, !dbg !766
  br i1 %302, label %304, label %303, !dbg !766

303:                                              ; preds = %300
  call void @klee_assert_fail(ptr noundef @.str.4, ptr noundef @.src, i32 noundef 44, ptr noundef @__PRETTY_FUNCTION__.checked_main) #8, !dbg !766
  unreachable, !dbg !766

304:                                              ; preds = %300
  %305 = load i32, ptr %14, align 4, !dbg !767
  %306 = add i32 %305, 1, !dbg !767
  store i32 %306, ptr %14, align 4, !dbg !767
  br label %282, !dbg !768, !llvm.loop !769

307:                                              ; preds = %282
  ret i32 0, !dbg !771

308:                                              ; preds = %25
  call void @abort(), !dbg !676
  unreachable, !dbg !676

309:                                              ; preds = %50
  call void @abort(), !dbg !690
  unreachable, !dbg !690

310:                                              ; preds = %66
  call void @abort(), !dbg !692
  unreachable, !dbg !692

311:                                              ; preds = %89
  call void @abort(), !dbg !701
  unreachable, !dbg !701

312:                                              ; preds = %105
  call void @abort(), !dbg !703
  unreachable, !dbg !703

313:                                              ; preds = %121
  call void @abort(), !dbg !706
  unreachable, !dbg !706

314:                                              ; preds = %137
  call void @abort(), !dbg !708
  unreachable, !dbg !708

315:                                              ; preds = %164
  call void @abort(), !dbg !726
  unreachable, !dbg !726

316:                                              ; preds = %180
  call void @abort(), !dbg !728
  unreachable, !dbg !728

317:                                              ; preds = %213
  call void @abort(), !dbg !751
  unreachable, !dbg !751

318:                                              ; preds = %229
  call void @abort(), !dbg !751
  unreachable, !dbg !751

319:                                              ; preds = %248
  call void @abort(), !dbg !753
  unreachable, !dbg !753

320:                                              ; preds = %265
  call void @abort(), !dbg !753
  unreachable, !dbg !753

321:                                              ; preds = %291
  call void @abort(), !dbg !766
  unreachable, !dbg !766
}

declare void @klee_make_symbolic(ptr noundef, i64 noundef, ptr noundef) #1

declare void @klee_assume(i64 noundef) #1

; Function Attrs: noreturn
declare void @klee_assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2

; Function Attrs: noinline nounwind sspstrong uwtable
define i32 @main() #3 !dbg !772 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i8, align 1
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !773, !DIExpression(), !774)
  %4 = call i32 @checked_main(), !dbg !775
  store i32 %4, ptr %2, align 4, !dbg !774
    #dbg_declare(ptr %3, !776, !DIExpression(), !778)
  call void @klee_make_symbolic(ptr noundef %3, i64 noundef 1, ptr noundef @.str.5), !dbg !779
  %5 = load i32, ptr %2, align 4, !dbg !780
  ret i32 %5, !dbg !781
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_type_mismatch_v1(ptr noundef %0, i64 noundef %1) #4 !dbg !782 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !795, !DIExpression(), !796)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !797, !DIExpression(), !798)
  %5 = load ptr, ptr %3, align 8, !dbg !799
  %6 = load i64, ptr %4, align 8, !dbg !800
  call void @_ZN7__ubsanL22handleTypeMismatchImplEP16TypeMismatchDatam(ptr noundef %5, i64 noundef %6), !dbg !801
  ret void, !dbg !802
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL22handleTypeMismatchImplEP16TypeMismatchDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !803 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i64, align 8
  %6 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !804, !DIExpression(), !805)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !806, !DIExpression(), !807)
    #dbg_declare(ptr %5, !808, !DIExpression(), !809)
  %7 = load ptr, ptr %3, align 8, !dbg !810
  %8 = getelementptr inbounds %struct.TypeMismatchData, ptr %7, i32 0, i32 2, !dbg !811
  %9 = load i8, ptr %8, align 8, !dbg !811
  %10 = zext i8 %9 to i32, !dbg !810
  %11 = zext i32 %10 to i64, !dbg !812
  call void @klee_overshift_check(i64 64, i64 %11), !dbg !812
  %12 = shl i64 1, %11, !dbg !812, !klee.check.shift !813
  store i64 %12, ptr %5, align 8, !dbg !809
    #dbg_declare(ptr %6, !814, !DIExpression(), !815)
  %13 = load i64, ptr %4, align 8, !dbg !816
  %14 = icmp ne i64 %13, 0, !dbg !816
  br i1 %14, label %23, label %15, !dbg !818

15:                                               ; preds = %2
  %16 = load ptr, ptr %3, align 8, !dbg !819
  %17 = getelementptr inbounds %struct.TypeMismatchData, ptr %16, i32 0, i32 3, !dbg !820
  %18 = load i8, ptr %17, align 1, !dbg !820
  %19 = zext i8 %18 to i32, !dbg !819
  %20 = icmp eq i32 %19, 10, !dbg !821
  %21 = zext i1 %20 to i64, !dbg !822
  %22 = select i1 %20, i32 2, i32 1, !dbg !822
  store i32 %22, ptr %6, align 4, !dbg !823
  br label %31, !dbg !824

23:                                               ; preds = %2
  %24 = load i64, ptr %4, align 8, !dbg !825
  %25 = load i64, ptr %5, align 8, !dbg !827
  %26 = sub i64 %25, 1, !dbg !828
  %27 = and i64 %24, %26, !dbg !829
  %28 = icmp ne i64 %27, 0, !dbg !825
  br i1 %28, label %29, label %30, !dbg !830

29:                                               ; preds = %23
  store i32 7, ptr %6, align 4, !dbg !831
  br label %31, !dbg !832

30:                                               ; preds = %23
  store i32 9, ptr %6, align 4, !dbg !833
  br label %31

31:                                               ; preds = %29, %30, %15
  %32 = load i32, ptr %6, align 4, !dbg !834
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %32) #8, !dbg !835
  unreachable, !dbg !835
}

; Function Attrs: mustprogress noinline noreturn sspstrong uwtable
define internal void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %0) #5 !dbg !836 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !839, !DIExpression(), !840)
  %3 = load i32, ptr %2, align 4, !dbg !841
  %4 = call noundef ptr @_ZN7__ubsanL19ConvertTypeToStringENS_9ErrorTypeE(i32 noundef %3), !dbg !842
  %5 = load i32, ptr %2, align 4, !dbg !843
  %6 = call noundef ptr @_ZN7__ubsanL10get_suffixENS_9ErrorTypeE(i32 noundef %5), !dbg !844
  call void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef %4, ptr noundef %6) #8, !dbg !845
  unreachable, !dbg !845
}

; Function Attrs: mustprogress noinline nounwind sspstrong uwtable
define internal noundef ptr @_ZN7__ubsanL19ConvertTypeToStringENS_9ErrorTypeE(i32 noundef %0) #6 !dbg !846 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store i32 %0, ptr %3, align 4
    #dbg_declare(ptr %3, !849, !DIExpression(), !850)
  %4 = load i32, ptr %3, align 4, !dbg !851
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
  ], !dbg !852

5:                                                ; preds = %1
  store ptr @.str.4.2, ptr %2, align 8, !dbg !853
  br label %42, !dbg !853

6:                                                ; preds = %1
  store ptr @.str.5.3, ptr %2, align 8, !dbg !856
  br label %42, !dbg !856

7:                                                ; preds = %1
  store ptr @.str.5.3, ptr %2, align 8, !dbg !857
  br label %42, !dbg !857

8:                                                ; preds = %1
  store ptr @.str.6, ptr %2, align 8, !dbg !858
  br label %42, !dbg !858

9:                                                ; preds = %1
  store ptr @.str.7, ptr %2, align 8, !dbg !859
  br label %42, !dbg !859

10:                                               ; preds = %1
  store ptr @.str.8, ptr %2, align 8, !dbg !860
  br label %42, !dbg !860

11:                                               ; preds = %1
  store ptr @.str.9, ptr %2, align 8, !dbg !861
  br label %42, !dbg !861

12:                                               ; preds = %1
  store ptr @.str.10, ptr %2, align 8, !dbg !862
  br label %42, !dbg !862

13:                                               ; preds = %1
  store ptr @.str.11, ptr %2, align 8, !dbg !863
  br label %42, !dbg !863

14:                                               ; preds = %1
  store ptr @.str.12, ptr %2, align 8, !dbg !864
  br label %42, !dbg !864

15:                                               ; preds = %1
  store ptr @.str.13, ptr %2, align 8, !dbg !865
  br label %42, !dbg !865

16:                                               ; preds = %1
  store ptr @.str.14, ptr %2, align 8, !dbg !866
  br label %42, !dbg !866

17:                                               ; preds = %1
  store ptr @.str.15, ptr %2, align 8, !dbg !867
  br label %42, !dbg !867

18:                                               ; preds = %1
  store ptr @.str.16, ptr %2, align 8, !dbg !868
  br label %42, !dbg !868

19:                                               ; preds = %1
  store ptr @.str.17, ptr %2, align 8, !dbg !869
  br label %42, !dbg !869

20:                                               ; preds = %1
  store ptr @.str.18, ptr %2, align 8, !dbg !870
  br label %42, !dbg !870

21:                                               ; preds = %1
  store ptr @.str.19, ptr %2, align 8, !dbg !871
  br label %42, !dbg !871

22:                                               ; preds = %1
  store ptr @.str.20, ptr %2, align 8, !dbg !872
  br label %42, !dbg !872

23:                                               ; preds = %1
  store ptr @.str.21, ptr %2, align 8, !dbg !873
  br label %42, !dbg !873

24:                                               ; preds = %1
  store ptr @.str.22, ptr %2, align 8, !dbg !874
  br label %42, !dbg !874

25:                                               ; preds = %1
  store ptr @.str.23, ptr %2, align 8, !dbg !875
  br label %42, !dbg !875

26:                                               ; preds = %1
  store ptr @.str.24, ptr %2, align 8, !dbg !876
  br label %42, !dbg !876

27:                                               ; preds = %1
  store ptr @.str.25, ptr %2, align 8, !dbg !877
  br label %42, !dbg !877

28:                                               ; preds = %1
  store ptr @.str.26, ptr %2, align 8, !dbg !878
  br label %42, !dbg !878

29:                                               ; preds = %1
  store ptr @.str.27, ptr %2, align 8, !dbg !879
  br label %42, !dbg !879

30:                                               ; preds = %1
  store ptr @.str.28, ptr %2, align 8, !dbg !880
  br label %42, !dbg !880

31:                                               ; preds = %1
  store ptr @.str.29, ptr %2, align 8, !dbg !881
  br label %42, !dbg !881

32:                                               ; preds = %1
  store ptr @.str.30, ptr %2, align 8, !dbg !882
  br label %42, !dbg !882

33:                                               ; preds = %1
  store ptr @.str.31, ptr %2, align 8, !dbg !883
  br label %42, !dbg !883

34:                                               ; preds = %1
  store ptr @.str.32, ptr %2, align 8, !dbg !884
  br label %42, !dbg !884

35:                                               ; preds = %1
  store ptr @.str.33, ptr %2, align 8, !dbg !885
  br label %42, !dbg !885

36:                                               ; preds = %1
  store ptr @.str.33, ptr %2, align 8, !dbg !886
  br label %42, !dbg !886

37:                                               ; preds = %1
  store ptr @.str.34, ptr %2, align 8, !dbg !887
  br label %42, !dbg !887

38:                                               ; preds = %1
  store ptr @.str.34, ptr %2, align 8, !dbg !888
  br label %42, !dbg !888

39:                                               ; preds = %1
  store ptr @.str.35, ptr %2, align 8, !dbg !889
  br label %42, !dbg !889

40:                                               ; preds = %1
  store ptr @.str.36, ptr %2, align 8, !dbg !890
  br label %42, !dbg !890

41:                                               ; preds = %1
  call void @abort(), !dbg !891
  unreachable, !dbg !891

42:                                               ; preds = %40, %39, %38, %37, %36, %35, %34, %33, %32, %31, %30, %29, %28, %27, %26, %25, %24, %23, %22, %21, %20, %19, %18, %17, %16, %15, %14, %13, %12, %11, %10, %9, %8, %7, %6, %5
  %43 = load ptr, ptr %2, align 8, !dbg !893
  ret ptr %43, !dbg !893
}

; Function Attrs: mustprogress noinline nounwind sspstrong uwtable
define internal noundef ptr @_ZN7__ubsanL10get_suffixENS_9ErrorTypeE(i32 noundef %0) #6 !dbg !894 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store i32 %0, ptr %3, align 4
    #dbg_declare(ptr %3, !895, !DIExpression(), !896)
  %4 = load i32, ptr %3, align 4, !dbg !897
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
  ], !dbg !898

5:                                                ; preds = %1
  store ptr @.str.37, ptr %2, align 8, !dbg !899
  br label %25, !dbg !899

6:                                                ; preds = %1, %1, %1, %1, %1, %1, %1, %1
  store ptr @.str.38, ptr %2, align 8, !dbg !901
  br label %25, !dbg !901

7:                                                ; preds = %1
  store ptr @.str.38, ptr %2, align 8, !dbg !902
  br label %25, !dbg !902

8:                                                ; preds = %1, %1
  store ptr @.str.39, ptr %2, align 8, !dbg !903
  br label %25, !dbg !903

9:                                                ; preds = %1, %1
  store ptr @.str.40, ptr %2, align 8, !dbg !904
  br label %25, !dbg !904

10:                                               ; preds = %1
  store ptr @.str.41, ptr %2, align 8, !dbg !905
  br label %25, !dbg !905

11:                                               ; preds = %1
  store ptr @.str.37, ptr %2, align 8, !dbg !906
  br label %25, !dbg !906

12:                                               ; preds = %1, %1
  store ptr @.str.42, ptr %2, align 8, !dbg !907
  br label %25, !dbg !907

13:                                               ; preds = %1, %1
  store ptr @.str.43, ptr %2, align 8, !dbg !908
  br label %25, !dbg !908

14:                                               ; preds = %1, %1
  store ptr @.str.39, ptr %2, align 8, !dbg !909
  br label %25, !dbg !909

15:                                               ; preds = %1
  store ptr @.str.38, ptr %2, align 8, !dbg !910
  br label %25, !dbg !910

16:                                               ; preds = %1
  store ptr @.str.44, ptr %2, align 8, !dbg !911
  br label %25, !dbg !911

17:                                               ; preds = %1
  store ptr @.str.45, ptr %2, align 8, !dbg !912
  br label %25, !dbg !912

18:                                               ; preds = %1
  store ptr @.str.38, ptr %2, align 8, !dbg !913
  br label %25, !dbg !913

19:                                               ; preds = %1
  store ptr @.str.39, ptr %2, align 8, !dbg !914
  br label %25, !dbg !914

20:                                               ; preds = %1, %1
  store ptr @.str.46, ptr %2, align 8, !dbg !915
  br label %25, !dbg !915

21:                                               ; preds = %1
  store ptr @.str.47, ptr %2, align 8, !dbg !916
  br label %25, !dbg !916

22:                                               ; preds = %1, %1, %1, %1
  store ptr @.str.48, ptr %2, align 8, !dbg !917
  br label %25, !dbg !917

23:                                               ; preds = %1, %1
  store ptr @.str.37, ptr %2, align 8, !dbg !918
  br label %25, !dbg !918

24:                                               ; preds = %1
  store ptr @.str.37, ptr %2, align 8, !dbg !919
  br label %25, !dbg !919

25:                                               ; preds = %24, %23, %22, %21, %20, %19, %18, %17, %16, %15, %14, %13, %12, %11, %10, %9, %8, %7, %6, %5
  %26 = load ptr, ptr %2, align 8, !dbg !920
  ret ptr %26, !dbg !920
}

; Function Attrs: mustprogress noinline noreturn sspstrong uwtable
define internal void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef %0, ptr noundef %1) #5 !dbg !921 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !924, !DIExpression(), !925)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !926, !DIExpression(), !927)
  %5 = load ptr, ptr %3, align 8, !dbg !928
  %6 = load ptr, ptr %4, align 8, !dbg !929
  call void @klee_report_error(ptr noundef @.str.3.1, i32 noundef 37, ptr noundef %5, ptr noundef %6) #8, !dbg !930
  unreachable, !dbg !930
}

; Function Attrs: noreturn
declare void @klee_report_error(ptr noundef, i32 noundef, ptr noundef, ptr noundef) #2

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_type_mismatch_v1_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !931 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !932, !DIExpression(), !933)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !934, !DIExpression(), !935)
  %5 = load ptr, ptr %3, align 8, !dbg !936
  %6 = load i64, ptr %4, align 8, !dbg !937
  call void @_ZN7__ubsanL22handleTypeMismatchImplEP16TypeMismatchDatam(ptr noundef %5, i64 noundef %6), !dbg !938
  ret void, !dbg !939
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_alignment_assumption(ptr noundef %0, i64 noundef %1, i64 noundef %2, i64 noundef %3) #4 !dbg !940 {
  %5 = alloca ptr, align 8
  %6 = alloca i64, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  store ptr %0, ptr %5, align 8
    #dbg_declare(ptr %5, !945, !DIExpression(), !946)
  store i64 %1, ptr %6, align 8
    #dbg_declare(ptr %6, !947, !DIExpression(), !948)
  store i64 %2, ptr %7, align 8
    #dbg_declare(ptr %7, !949, !DIExpression(), !950)
  store i64 %3, ptr %8, align 8
    #dbg_declare(ptr %8, !951, !DIExpression(), !952)
  %9 = load ptr, ptr %5, align 8, !dbg !953
  %10 = load i64, ptr %6, align 8, !dbg !954
  %11 = load i64, ptr %7, align 8, !dbg !955
  %12 = load i64, ptr %8, align 8, !dbg !956
  call void @_ZN7__ubsanL29handleAlignmentAssumptionImplEP23AlignmentAssumptionDatammm(ptr noundef %9, i64 noundef %10, i64 noundef %11, i64 noundef %12), !dbg !957
  ret void, !dbg !958
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL29handleAlignmentAssumptionImplEP23AlignmentAssumptionDatammm(ptr noundef %0, i64 noundef %1, i64 noundef %2, i64 noundef %3) #4 !dbg !959 {
  %5 = alloca ptr, align 8
  %6 = alloca i64, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  %9 = alloca i32, align 4
  store ptr %0, ptr %5, align 8
    #dbg_declare(ptr %5, !960, !DIExpression(), !961)
  store i64 %1, ptr %6, align 8
    #dbg_declare(ptr %6, !962, !DIExpression(), !963)
  store i64 %2, ptr %7, align 8
    #dbg_declare(ptr %7, !964, !DIExpression(), !965)
  store i64 %3, ptr %8, align 8
    #dbg_declare(ptr %8, !966, !DIExpression(), !967)
    #dbg_declare(ptr %9, !968, !DIExpression(), !969)
  store i32 8, ptr %9, align 4, !dbg !969
  %10 = load i32, ptr %9, align 4, !dbg !970
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %10) #8, !dbg !971
  unreachable, !dbg !971
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_alignment_assumption_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2, i64 noundef %3) #4 !dbg !972 {
  %5 = alloca ptr, align 8
  %6 = alloca i64, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  store ptr %0, ptr %5, align 8
    #dbg_declare(ptr %5, !973, !DIExpression(), !974)
  store i64 %1, ptr %6, align 8
    #dbg_declare(ptr %6, !975, !DIExpression(), !976)
  store i64 %2, ptr %7, align 8
    #dbg_declare(ptr %7, !977, !DIExpression(), !978)
  store i64 %3, ptr %8, align 8
    #dbg_declare(ptr %8, !979, !DIExpression(), !980)
  %9 = load ptr, ptr %5, align 8, !dbg !981
  %10 = load i64, ptr %6, align 8, !dbg !982
  %11 = load i64, ptr %7, align 8, !dbg !983
  %12 = load i64, ptr %8, align 8, !dbg !984
  call void @_ZN7__ubsanL29handleAlignmentAssumptionImplEP23AlignmentAssumptionDatammm(ptr noundef %9, i64 noundef %10, i64 noundef %11, i64 noundef %12), !dbg !985
  ret void, !dbg !986
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_add_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !987 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !995, !DIExpression(), !996)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !997, !DIExpression(), !996)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !998, !DIExpression(), !996)
  %7 = load ptr, ptr %4, align 8, !dbg !996
  %8 = load i64, ptr %5, align 8, !dbg !996
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.49), !dbg !996
  ret void, !dbg !996
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %0, i64 noundef %1, ptr noundef %2) #4 !dbg !999 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca ptr, align 8
  %7 = alloca i8, align 1
  %8 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1002, !DIExpression(), !1003)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1004, !DIExpression(), !1005)
  store ptr %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1006, !DIExpression(), !1007)
    #dbg_declare(ptr %7, !1008, !DIExpression(), !1009)
  %9 = load ptr, ptr %4, align 8, !dbg !1010
  %10 = getelementptr inbounds %struct.OverflowData, ptr %9, i32 0, i32 1, !dbg !1011
  %11 = load ptr, ptr %10, align 8, !dbg !1011
  %12 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %11), !dbg !1012
  %13 = zext i1 %12 to i8, !dbg !1009
  store i8 %13, ptr %7, align 1, !dbg !1009
    #dbg_declare(ptr %8, !1013, !DIExpression(), !1014)
  %14 = load i8, ptr %7, align 1, !dbg !1015
  %15 = trunc i8 %14 to i1, !dbg !1015
  %16 = zext i1 %15 to i64, !dbg !1015
  %17 = select i1 %15, i32 10, i32 11, !dbg !1015
  store i32 %17, ptr %8, align 4, !dbg !1014
  %18 = load i32, ptr %8, align 4, !dbg !1016
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %18) #8, !dbg !1017
  unreachable, !dbg !1017
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define linkonce_odr noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %0) #4 comdat align 2 !dbg !1018 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1019, !DIExpression(), !1021)
  %3 = load ptr, ptr %2, align 8
  %4 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %3), !dbg !1022
  br i1 %4, label %5, label %11, !dbg !1023

5:                                                ; preds = %1
  %6 = getelementptr inbounds %"class.__ubsan::TypeDescriptor", ptr %3, i32 0, i32 1, !dbg !1024
  %7 = load i16, ptr %6, align 2, !dbg !1024
  %8 = zext i16 %7 to i32, !dbg !1024
  %9 = and i32 %8, 1, !dbg !1025
  %10 = icmp ne i32 %9, 0, !dbg !1026
  br label %11

11:                                               ; preds = %5, %1
  %12 = phi i1 [ false, %1 ], [ %10, %5 ], !dbg !1021
  ret i1 %12, !dbg !1027
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define linkonce_odr noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %0) #4 comdat align 2 !dbg !1028 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1029, !DIExpression(), !1030)
  %3 = load ptr, ptr %2, align 8
  %4 = call noundef i32 @_ZNK7__ubsan14TypeDescriptor7getKindEv(ptr noundef nonnull align 2 dereferenceable(5) %3), !dbg !1031
  %5 = icmp eq i32 %4, 0, !dbg !1032
  ret i1 %5, !dbg !1033
}

; Function Attrs: mustprogress noinline nounwind sspstrong uwtable
define linkonce_odr noundef i32 @_ZNK7__ubsan14TypeDescriptor7getKindEv(ptr noundef nonnull align 2 dereferenceable(5) %0) #6 comdat align 2 !dbg !1034 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1035, !DIExpression(), !1036)
  %3 = load ptr, ptr %2, align 8
  %4 = getelementptr inbounds %"class.__ubsan::TypeDescriptor", ptr %3, i32 0, i32 0, !dbg !1037
  %5 = load i16, ptr %4, align 2, !dbg !1037
  %6 = zext i16 %5 to i32, !dbg !1038
  ret i32 %6, !dbg !1039
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_add_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1040 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1041, !DIExpression(), !1042)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1043, !DIExpression(), !1042)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1044, !DIExpression(), !1042)
  %7 = load ptr, ptr %4, align 8, !dbg !1042
  %8 = load i64, ptr %5, align 8, !dbg !1042
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.49), !dbg !1042
  ret void, !dbg !1042
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_sub_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1045 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1046, !DIExpression(), !1047)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1048, !DIExpression(), !1047)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1049, !DIExpression(), !1047)
  %7 = load ptr, ptr %4, align 8, !dbg !1047
  %8 = load i64, ptr %5, align 8, !dbg !1047
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.1.50), !dbg !1047
  ret void, !dbg !1047
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_sub_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1050 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1051, !DIExpression(), !1052)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1053, !DIExpression(), !1052)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1054, !DIExpression(), !1052)
  %7 = load ptr, ptr %4, align 8, !dbg !1052
  %8 = load i64, ptr %5, align 8, !dbg !1052
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.1.50), !dbg !1052
  ret void, !dbg !1052
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_mul_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1055 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1056, !DIExpression(), !1057)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1058, !DIExpression(), !1057)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1059, !DIExpression(), !1057)
  %7 = load ptr, ptr %4, align 8, !dbg !1057
  %8 = load i64, ptr %5, align 8, !dbg !1057
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.2.51), !dbg !1057
  ret void, !dbg !1057
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_mul_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1060 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1061, !DIExpression(), !1062)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1063, !DIExpression(), !1062)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1064, !DIExpression(), !1062)
  %7 = load ptr, ptr %4, align 8, !dbg !1062
  %8 = load i64, ptr %5, align 8, !dbg !1062
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.2.51), !dbg !1062
  ret void, !dbg !1062
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_negate_overflow(ptr noundef %0, i64 noundef %1) #4 !dbg !1065 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1068, !DIExpression(), !1069)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1070, !DIExpression(), !1071)
  %5 = load ptr, ptr %3, align 8, !dbg !1072
  %6 = load i64, ptr %4, align 8, !dbg !1073
  call void @_ZN7__ubsanL24handleNegateOverflowImplEP12OverflowDatam(ptr noundef %5, i64 noundef %6), !dbg !1074
  ret void, !dbg !1075
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL24handleNegateOverflowImplEP12OverflowDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1076 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i8, align 1
  %6 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1077, !DIExpression(), !1078)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1079, !DIExpression(), !1080)
    #dbg_declare(ptr %5, !1081, !DIExpression(), !1082)
  %7 = load ptr, ptr %3, align 8, !dbg !1083
  %8 = getelementptr inbounds %struct.OverflowData, ptr %7, i32 0, i32 1, !dbg !1084
  %9 = load ptr, ptr %8, align 8, !dbg !1084
  %10 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %9), !dbg !1085
  %11 = zext i1 %10 to i8, !dbg !1082
  store i8 %11, ptr %5, align 1, !dbg !1082
    #dbg_declare(ptr %6, !1086, !DIExpression(), !1087)
  %12 = load i8, ptr %5, align 1, !dbg !1088
  %13 = trunc i8 %12 to i1, !dbg !1088
  %14 = zext i1 %13 to i64, !dbg !1088
  %15 = select i1 %13, i32 10, i32 11, !dbg !1088
  store i32 %15, ptr %6, align 4, !dbg !1087
  %16 = load i32, ptr %6, align 4, !dbg !1089
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %16) #8, !dbg !1090
  unreachable, !dbg !1090
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_negate_overflow_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1091 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1092, !DIExpression(), !1093)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1094, !DIExpression(), !1095)
  %5 = load ptr, ptr %3, align 8, !dbg !1096
  %6 = load i64, ptr %4, align 8, !dbg !1097
  call void @_ZN7__ubsanL24handleNegateOverflowImplEP12OverflowDatam(ptr noundef %5, i64 noundef %6), !dbg !1098
  ret void, !dbg !1099
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_divrem_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1100 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1101, !DIExpression(), !1102)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1103, !DIExpression(), !1104)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1105, !DIExpression(), !1106)
  %7 = load ptr, ptr %4, align 8, !dbg !1107
  %8 = load i64, ptr %5, align 8, !dbg !1108
  %9 = load i64, ptr %6, align 8, !dbg !1109
  call void @_ZN7__ubsanL24handleDivremOverflowImplEP12OverflowDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1110
  ret void, !dbg !1111
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL24handleDivremOverflowImplEP12OverflowDatamm(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1112 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  %7 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1113, !DIExpression(), !1114)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1115, !DIExpression(), !1116)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1117, !DIExpression(), !1118)
  %8 = load ptr, ptr %4, align 8, !dbg !1119
  %9 = getelementptr inbounds %struct.OverflowData, ptr %8, i32 0, i32 1, !dbg !1121
  %10 = load ptr, ptr %9, align 8, !dbg !1121
  %11 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %10), !dbg !1122
  br i1 %11, label %12, label %13, !dbg !1123

12:                                               ; preds = %3
  call void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef @.str.49.52, ptr noundef @.str.39) #8, !dbg !1124
  unreachable, !dbg !1124

13:                                               ; preds = %3
    #dbg_declare(ptr %7, !1125, !DIExpression(), !1127)
  store i32 13, ptr %7, align 4, !dbg !1127
  %14 = load i32, ptr %7, align 4, !dbg !1128
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %14) #8, !dbg !1129
  unreachable, !dbg !1129
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_divrem_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1130 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1131, !DIExpression(), !1132)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1133, !DIExpression(), !1134)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1135, !DIExpression(), !1136)
  %7 = load ptr, ptr %4, align 8, !dbg !1137
  %8 = load i64, ptr %5, align 8, !dbg !1138
  %9 = load i64, ptr %6, align 8, !dbg !1139
  call void @_ZN7__ubsanL24handleDivremOverflowImplEP12OverflowDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1140
  ret void, !dbg !1141
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_shift_out_of_bounds(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1142 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1147, !DIExpression(), !1148)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1149, !DIExpression(), !1150)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1151, !DIExpression(), !1152)
  %7 = load ptr, ptr %4, align 8, !dbg !1153
  %8 = load i64, ptr %5, align 8, !dbg !1154
  %9 = load i64, ptr %6, align 8, !dbg !1155
  call void @_ZN7__ubsanL26handleShiftOutOfBoundsImplEP20ShiftOutOfBoundsDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1156
  ret void, !dbg !1157
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL26handleShiftOutOfBoundsImplEP20ShiftOutOfBoundsDatamm(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1158 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1159, !DIExpression(), !1160)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1161, !DIExpression(), !1162)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1163, !DIExpression(), !1164)
  call void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef @.str.50, ptr noundef @.str.39) #8, !dbg !1165
  unreachable, !dbg !1165
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_shift_out_of_bounds_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1166 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1167, !DIExpression(), !1168)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1169, !DIExpression(), !1170)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1171, !DIExpression(), !1172)
  %7 = load ptr, ptr %4, align 8, !dbg !1173
  %8 = load i64, ptr %5, align 8, !dbg !1174
  %9 = load i64, ptr %6, align 8, !dbg !1175
  call void @_ZN7__ubsanL26handleShiftOutOfBoundsImplEP20ShiftOutOfBoundsDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1176
  ret void, !dbg !1177
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_out_of_bounds(ptr noundef %0, i64 noundef %1) #4 !dbg !1178 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1183, !DIExpression(), !1184)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1185, !DIExpression(), !1186)
  %5 = load ptr, ptr %3, align 8, !dbg !1187
  %6 = load i64, ptr %4, align 8, !dbg !1188
  call void @_ZN7__ubsanL21handleOutOfBoundsImplEP15OutOfBoundsDatam(ptr noundef %5, i64 noundef %6), !dbg !1189
  ret void, !dbg !1190
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL21handleOutOfBoundsImplEP15OutOfBoundsDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1191 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1192, !DIExpression(), !1193)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1194, !DIExpression(), !1195)
    #dbg_declare(ptr %5, !1196, !DIExpression(), !1197)
  store i32 22, ptr %5, align 4, !dbg !1197
  %6 = load i32, ptr %5, align 4, !dbg !1198
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %6) #8, !dbg !1199
  unreachable, !dbg !1199
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_out_of_bounds_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1200 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1201, !DIExpression(), !1202)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1203, !DIExpression(), !1204)
  %5 = load ptr, ptr %3, align 8, !dbg !1205
  %6 = load i64, ptr %4, align 8, !dbg !1206
  call void @_ZN7__ubsanL21handleOutOfBoundsImplEP15OutOfBoundsDatam(ptr noundef %5, i64 noundef %6), !dbg !1207
  ret void, !dbg !1208
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_builtin_unreachable(ptr noundef %0) #4 !dbg !1209 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1214, !DIExpression(), !1215)
  %3 = load ptr, ptr %2, align 8, !dbg !1216
  call void @_ZN7__ubsanL28handleBuiltinUnreachableImplEP15UnreachableData(ptr noundef %3), !dbg !1217
  ret void, !dbg !1218
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL28handleBuiltinUnreachableImplEP15UnreachableData(ptr noundef %0) #4 !dbg !1219 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1220, !DIExpression(), !1221)
    #dbg_declare(ptr %3, !1222, !DIExpression(), !1223)
  store i32 23, ptr %3, align 4, !dbg !1223
  %4 = load i32, ptr %3, align 4, !dbg !1224
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %4) #8, !dbg !1225
  unreachable, !dbg !1225
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_missing_return(ptr noundef %0) #4 !dbg !1226 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1227, !DIExpression(), !1228)
  %3 = load ptr, ptr %2, align 8, !dbg !1229
  call void @_ZN7__ubsanL23handleMissingReturnImplEP15UnreachableData(ptr noundef %3), !dbg !1230
  ret void, !dbg !1231
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL23handleMissingReturnImplEP15UnreachableData(ptr noundef %0) #4 !dbg !1232 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1233, !DIExpression(), !1234)
    #dbg_declare(ptr %3, !1235, !DIExpression(), !1236)
  store i32 24, ptr %3, align 4, !dbg !1236
  %4 = load i32, ptr %3, align 4, !dbg !1237
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %4) #8, !dbg !1238
  unreachable, !dbg !1238
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_vla_bound_not_positive(ptr noundef %0, i64 noundef %1) #4 !dbg !1239 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1244, !DIExpression(), !1245)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1246, !DIExpression(), !1247)
  %5 = load ptr, ptr %3, align 8, !dbg !1248
  %6 = load i64, ptr %4, align 8, !dbg !1249
  call void @_ZN7__ubsanL25handleVLABoundNotPositiveEP12VLABoundDatam(ptr noundef %5, i64 noundef %6), !dbg !1250
  ret void, !dbg !1251
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL25handleVLABoundNotPositiveEP12VLABoundDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1252 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1253, !DIExpression(), !1254)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1255, !DIExpression(), !1256)
    #dbg_declare(ptr %5, !1257, !DIExpression(), !1258)
  store i32 25, ptr %5, align 4, !dbg !1258
  %6 = load i32, ptr %5, align 4, !dbg !1259
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %6) #8, !dbg !1260
  unreachable, !dbg !1260
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_vla_bound_not_positive_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1261 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1262, !DIExpression(), !1263)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1264, !DIExpression(), !1265)
  %5 = load ptr, ptr %3, align 8, !dbg !1266
  %6 = load i64, ptr %4, align 8, !dbg !1267
  call void @_ZN7__ubsanL25handleVLABoundNotPositiveEP12VLABoundDatam(ptr noundef %5, i64 noundef %6), !dbg !1268
  ret void, !dbg !1269
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_float_cast_overflow(ptr noundef %0, i64 noundef %1) #4 !dbg !1270 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1274, !DIExpression(), !1275)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1276, !DIExpression(), !1277)
  %5 = load ptr, ptr %3, align 8, !dbg !1278
  %6 = load i64, ptr %4, align 8, !dbg !1279
  call void @_ZN7__ubsanL23handleFloatCastOverflowEPvm(ptr noundef %5, i64 noundef %6), !dbg !1280
  ret void, !dbg !1281
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL23handleFloatCastOverflowEPvm(ptr noundef %0, i64 noundef %1) #4 !dbg !1282 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1283, !DIExpression(), !1284)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1285, !DIExpression(), !1286)
    #dbg_declare(ptr %5, !1287, !DIExpression(), !1288)
  store i32 26, ptr %5, align 4, !dbg !1288
  %6 = load i32, ptr %5, align 4, !dbg !1289
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %6) #8, !dbg !1290
  unreachable, !dbg !1290
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_float_cast_overflow_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1291 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1292, !DIExpression(), !1293)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1294, !DIExpression(), !1295)
  %5 = load ptr, ptr %3, align 8, !dbg !1296
  %6 = load i64, ptr %4, align 8, !dbg !1297
  call void @_ZN7__ubsanL23handleFloatCastOverflowEPvm(ptr noundef %5, i64 noundef %6), !dbg !1298
  ret void, !dbg !1299
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_load_invalid_value(ptr noundef %0, i64 noundef %1) #4 !dbg !1300 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1305, !DIExpression(), !1306)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1307, !DIExpression(), !1308)
  %5 = load ptr, ptr %3, align 8, !dbg !1309
  %6 = load i64, ptr %4, align 8, !dbg !1310
  call void @_ZN7__ubsanL22handleLoadInvalidValueEP16InvalidValueDatam(ptr noundef %5, i64 noundef %6), !dbg !1311
  ret void, !dbg !1312
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL22handleLoadInvalidValueEP16InvalidValueDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1313 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1314, !DIExpression(), !1315)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1316, !DIExpression(), !1317)
  call void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef @.str.51, ptr noundef @.str.46) #8, !dbg !1318
  unreachable, !dbg !1318
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_load_invalid_value_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1319 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1320, !DIExpression(), !1321)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1322, !DIExpression(), !1323)
  %5 = load ptr, ptr %3, align 8, !dbg !1324
  %6 = load i64, ptr %4, align 8, !dbg !1325
  call void @_ZN7__ubsanL22handleLoadInvalidValueEP16InvalidValueDatam(ptr noundef %5, i64 noundef %6), !dbg !1326
  ret void, !dbg !1327
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_implicit_conversion(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1328 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1338, !DIExpression(), !1339)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1340, !DIExpression(), !1341)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1342, !DIExpression(), !1343)
  %7 = load ptr, ptr %4, align 8, !dbg !1344
  %8 = load i64, ptr %5, align 8, !dbg !1345
  %9 = load i64, ptr %6, align 8, !dbg !1346
  call void @_ZN7__ubsanL24handleImplicitConversionEP22ImplicitConversionDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1347
  ret void, !dbg !1348
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL24handleImplicitConversionEP22ImplicitConversionDatamm(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1349 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  %7 = alloca i32, align 4
  %8 = alloca ptr, align 8
  %9 = alloca ptr, align 8
  %10 = alloca i8, align 1
  %11 = alloca i8, align 1
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1350, !DIExpression(), !1351)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1352, !DIExpression(), !1353)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1354, !DIExpression(), !1355)
    #dbg_declare(ptr %7, !1356, !DIExpression(), !1357)
  store i32 0, ptr %7, align 4, !dbg !1357
    #dbg_declare(ptr %8, !1358, !DIExpression(), !1359)
  %12 = load ptr, ptr %4, align 8, !dbg !1360
  %13 = getelementptr inbounds %struct.ImplicitConversionData, ptr %12, i32 0, i32 1, !dbg !1361
  %14 = load ptr, ptr %13, align 8, !dbg !1361
  store ptr %14, ptr %8, align 8, !dbg !1359
    #dbg_declare(ptr %9, !1362, !DIExpression(), !1363)
  %15 = load ptr, ptr %4, align 8, !dbg !1364
  %16 = getelementptr inbounds %struct.ImplicitConversionData, ptr %15, i32 0, i32 2, !dbg !1365
  %17 = load ptr, ptr %16, align 8, !dbg !1365
  store ptr %17, ptr %9, align 8, !dbg !1363
    #dbg_declare(ptr %10, !1366, !DIExpression(), !1367)
  %18 = load ptr, ptr %8, align 8, !dbg !1368
  %19 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %18), !dbg !1369
  %20 = zext i1 %19 to i8, !dbg !1367
  store i8 %20, ptr %10, align 1, !dbg !1367
    #dbg_declare(ptr %11, !1370, !DIExpression(), !1371)
  %21 = load ptr, ptr %9, align 8, !dbg !1372
  %22 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %21), !dbg !1373
  %23 = zext i1 %22 to i8, !dbg !1371
  store i8 %23, ptr %11, align 1, !dbg !1371
  %24 = load ptr, ptr %4, align 8, !dbg !1374
  %25 = getelementptr inbounds %struct.ImplicitConversionData, ptr %24, i32 0, i32 3, !dbg !1375
  %26 = load i8, ptr %25, align 8, !dbg !1375
  %27 = zext i8 %26 to i32, !dbg !1374
  switch i32 %27, label %40 [
    i32 0, label %28
    i32 1, label %36
    i32 2, label %37
    i32 3, label %38
    i32 4, label %39
  ], !dbg !1376

28:                                               ; preds = %3
  %29 = load i8, ptr %10, align 1, !dbg !1377
  %30 = trunc i8 %29 to i1, !dbg !1377
  br i1 %30, label %35, label %31, !dbg !1381

31:                                               ; preds = %28
  %32 = load i8, ptr %11, align 1, !dbg !1382
  %33 = trunc i8 %32 to i1, !dbg !1382
  br i1 %33, label %35, label %34, !dbg !1383

34:                                               ; preds = %31
  store i32 16, ptr %7, align 4, !dbg !1384
  br label %40, !dbg !1386

35:                                               ; preds = %31, %28
  store i32 17, ptr %7, align 4, !dbg !1387
  br label %40

36:                                               ; preds = %3
  store i32 16, ptr %7, align 4, !dbg !1389
  br label %40, !dbg !1390

37:                                               ; preds = %3
  store i32 17, ptr %7, align 4, !dbg !1391
  br label %40, !dbg !1392

38:                                               ; preds = %3
  store i32 18, ptr %7, align 4, !dbg !1393
  br label %40, !dbg !1394

39:                                               ; preds = %3
  store i32 19, ptr %7, align 4, !dbg !1395
  br label %40, !dbg !1396

40:                                               ; preds = %34, %35, %3, %39, %38, %37, %36
  %41 = load i32, ptr %7, align 4, !dbg !1397
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %41) #8, !dbg !1398
  unreachable, !dbg !1398
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_implicit_conversion_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1399 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1400, !DIExpression(), !1401)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1402, !DIExpression(), !1403)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1404, !DIExpression(), !1405)
  %7 = load ptr, ptr %4, align 8, !dbg !1406
  %8 = load i64, ptr %5, align 8, !dbg !1407
  %9 = load i64, ptr %6, align 8, !dbg !1408
  call void @_ZN7__ubsanL24handleImplicitConversionEP22ImplicitConversionDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1409
  ret void, !dbg !1410
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_invalid_builtin(ptr noundef %0) #4 !dbg !1411 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1416, !DIExpression(), !1417)
  %3 = load ptr, ptr %2, align 8, !dbg !1418
  call void @_ZN7__ubsanL20handleInvalidBuiltinEP18InvalidBuiltinData(ptr noundef %3), !dbg !1419
  ret void, !dbg !1420
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL20handleInvalidBuiltinEP18InvalidBuiltinData(ptr noundef %0) #4 !dbg !1421 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1422, !DIExpression(), !1423)
    #dbg_declare(ptr %3, !1424, !DIExpression(), !1425)
  store i32 14, ptr %3, align 4, !dbg !1425
  %4 = load i32, ptr %3, align 4, !dbg !1426
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %4) #8, !dbg !1427
  unreachable, !dbg !1427
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_invalid_builtin_abort(ptr noundef %0) #4 !dbg !1428 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1429, !DIExpression(), !1430)
  %3 = load ptr, ptr %2, align 8, !dbg !1431
  call void @_ZN7__ubsanL20handleInvalidBuiltinEP18InvalidBuiltinData(ptr noundef %3), !dbg !1432
  ret void, !dbg !1433
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nonnull_return_v1(ptr noundef %0, ptr noundef %1) #4 !dbg !1434 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1440, !DIExpression(), !1441)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1442, !DIExpression(), !1443)
  %5 = load ptr, ptr %3, align 8, !dbg !1444
  %6 = load ptr, ptr %4, align 8, !dbg !1445
  call void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %5, ptr noundef %6, i1 noundef zeroext true), !dbg !1446
  ret void, !dbg !1447
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %0, ptr noundef %1, i1 noundef zeroext %2) #4 !dbg !1448 {
  %4 = alloca ptr, align 8
  %5 = alloca ptr, align 8
  %6 = alloca i8, align 1
  %7 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1451, !DIExpression(), !1452)
  store ptr %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1453, !DIExpression(), !1454)
  %8 = zext i1 %2 to i8
  store i8 %8, ptr %6, align 1
    #dbg_declare(ptr %6, !1455, !DIExpression(), !1456)
    #dbg_declare(ptr %7, !1457, !DIExpression(), !1458)
  %9 = load i8, ptr %6, align 1, !dbg !1459
  %10 = trunc i8 %9 to i1, !dbg !1459
  %11 = zext i1 %10 to i64, !dbg !1459
  %12 = select i1 %10, i32 30, i32 31, !dbg !1459
  store i32 %12, ptr %7, align 4, !dbg !1458
  %13 = load i32, ptr %7, align 4, !dbg !1460
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %13) #8, !dbg !1461
  unreachable, !dbg !1461
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nonnull_return_v1_abort(ptr noundef %0, ptr noundef %1) #4 !dbg !1462 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1463, !DIExpression(), !1464)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1465, !DIExpression(), !1466)
  %5 = load ptr, ptr %3, align 8, !dbg !1467
  %6 = load ptr, ptr %4, align 8, !dbg !1468
  call void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %5, ptr noundef %6, i1 noundef zeroext true), !dbg !1469
  ret void, !dbg !1470
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nullability_return_v1(ptr noundef %0, ptr noundef %1) #4 !dbg !1471 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1472, !DIExpression(), !1473)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1474, !DIExpression(), !1475)
  %5 = load ptr, ptr %3, align 8, !dbg !1476
  %6 = load ptr, ptr %4, align 8, !dbg !1477
  call void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %5, ptr noundef %6, i1 noundef zeroext false), !dbg !1478
  ret void, !dbg !1479
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nullability_return_v1_abort(ptr noundef %0, ptr noundef %1) #4 !dbg !1480 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1481, !DIExpression(), !1482)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1483, !DIExpression(), !1484)
  %5 = load ptr, ptr %3, align 8, !dbg !1485
  %6 = load ptr, ptr %4, align 8, !dbg !1486
  call void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %5, ptr noundef %6, i1 noundef zeroext false), !dbg !1487
  ret void, !dbg !1488
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nonnull_arg(ptr noundef %0) #4 !dbg !1489 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1494, !DIExpression(), !1495)
  %3 = load ptr, ptr %2, align 8, !dbg !1496
  call void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %3, i1 noundef zeroext true), !dbg !1497
  ret void, !dbg !1498
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %0, i1 noundef zeroext %1) #4 !dbg !1499 {
  %3 = alloca ptr, align 8
  %4 = alloca i8, align 1
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1502, !DIExpression(), !1503)
  %6 = zext i1 %1 to i8
  store i8 %6, ptr %4, align 1
    #dbg_declare(ptr %4, !1504, !DIExpression(), !1505)
    #dbg_declare(ptr %5, !1506, !DIExpression(), !1507)
  %7 = load i8, ptr %4, align 1, !dbg !1508
  %8 = trunc i8 %7 to i1, !dbg !1508
  %9 = zext i1 %8 to i64, !dbg !1508
  %10 = select i1 %8, i32 32, i32 33, !dbg !1508
  store i32 %10, ptr %5, align 4, !dbg !1507
  %11 = load i32, ptr %5, align 4, !dbg !1509
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %11) #8, !dbg !1510
  unreachable, !dbg !1510
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nonnull_arg_abort(ptr noundef %0) #4 !dbg !1511 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1512, !DIExpression(), !1513)
  %3 = load ptr, ptr %2, align 8, !dbg !1514
  call void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %3, i1 noundef zeroext true), !dbg !1515
  ret void, !dbg !1516
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nullability_arg(ptr noundef %0) #4 !dbg !1517 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1518, !DIExpression(), !1519)
  %3 = load ptr, ptr %2, align 8, !dbg !1520
  call void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %3, i1 noundef zeroext false), !dbg !1521
  ret void, !dbg !1522
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nullability_arg_abort(ptr noundef %0) #4 !dbg !1523 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1524, !DIExpression(), !1525)
  %3 = load ptr, ptr %2, align 8, !dbg !1526
  call void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %3, i1 noundef zeroext false), !dbg !1527
  ret void, !dbg !1528
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_pointer_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1529 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1534, !DIExpression(), !1535)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1536, !DIExpression(), !1537)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1538, !DIExpression(), !1539)
  %7 = load ptr, ptr %4, align 8, !dbg !1540
  %8 = load i64, ptr %5, align 8, !dbg !1541
  %9 = load i64, ptr %6, align 8, !dbg !1542
  call void @_ZN7__ubsanL25handlePointerOverflowImplEP19PointerOverflowDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1543
  ret void, !dbg !1544
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL25handlePointerOverflowImplEP19PointerOverflowDatamm(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1545 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  %7 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1546, !DIExpression(), !1547)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1548, !DIExpression(), !1549)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1550, !DIExpression(), !1551)
    #dbg_declare(ptr %7, !1552, !DIExpression(), !1553)
  %8 = load i64, ptr %5, align 8, !dbg !1554
  %9 = icmp eq i64 %8, 0, !dbg !1556
  %10 = load i64, ptr %6, align 8
  %11 = icmp eq i64 %10, 0
  %or.cond = select i1 %9, i1 %11, i1 false, !dbg !1557
  br i1 %or.cond, label %12, label %13, !dbg !1557

12:                                               ; preds = %3
  store i32 3, ptr %7, align 4, !dbg !1558
  br label %26, !dbg !1559

13:                                               ; preds = %3
  %14 = load i64, ptr %5, align 8, !dbg !1560
  %15 = icmp eq i64 %14, 0, !dbg !1562
  %16 = load i64, ptr %6, align 8
  %17 = icmp ne i64 %16, 0
  %or.cond3 = select i1 %15, i1 %17, i1 false, !dbg !1563
  br i1 %or.cond3, label %18, label %19, !dbg !1563

18:                                               ; preds = %13
  store i32 4, ptr %7, align 4, !dbg !1564
  br label %26, !dbg !1565

19:                                               ; preds = %13
  %20 = load i64, ptr %5, align 8, !dbg !1566
  %21 = icmp ne i64 %20, 0, !dbg !1568
  %22 = load i64, ptr %6, align 8
  %23 = icmp eq i64 %22, 0
  %or.cond5 = select i1 %21, i1 %23, i1 false, !dbg !1569
  br i1 %or.cond5, label %24, label %25, !dbg !1569

24:                                               ; preds = %19
  store i32 5, ptr %7, align 4, !dbg !1570
  br label %26, !dbg !1571

25:                                               ; preds = %19
  store i32 6, ptr %7, align 4, !dbg !1572
  br label %26

26:                                               ; preds = %18, %25, %24, %12
  %27 = load i32, ptr %7, align 4, !dbg !1573
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %27) #8, !dbg !1574
  unreachable, !dbg !1574
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_pointer_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1575 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1576, !DIExpression(), !1577)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1578, !DIExpression(), !1579)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1580, !DIExpression(), !1581)
  %7 = load ptr, ptr %4, align 8, !dbg !1582
  %8 = load i64, ptr %5, align 8, !dbg !1583
  %9 = load i64, ptr %6, align 8, !dbg !1584
  call void @_ZN7__ubsanL25handlePointerOverflowImplEP19PointerOverflowDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1585
  ret void, !dbg !1586
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_function_type_mismatch(ptr noundef %0, i64 noundef %1) #4 !dbg !1587 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1592, !DIExpression(), !1593)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1594, !DIExpression(), !1595)
  %5 = load ptr, ptr %3, align 8, !dbg !1596
  %6 = load i64, ptr %4, align 8, !dbg !1597
  call void @_ZN7__ubsanL26handleFunctionTypeMismatchEP24FunctionTypeMismatchDatam(ptr noundef %5, i64 noundef %6), !dbg !1598
  ret void, !dbg !1599
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL26handleFunctionTypeMismatchEP24FunctionTypeMismatchDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1600 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1601, !DIExpression(), !1602)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1603, !DIExpression(), !1604)
    #dbg_declare(ptr %5, !1605, !DIExpression(), !1606)
  store i32 29, ptr %5, align 4, !dbg !1606
  %6 = load i32, ptr %5, align 4, !dbg !1607
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %6) #8, !dbg !1608
  unreachable, !dbg !1608
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_function_type_mismatch_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1609 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1610, !DIExpression(), !1611)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1612, !DIExpression(), !1613)
  %5 = load ptr, ptr %3, align 8, !dbg !1614
  %6 = load i64, ptr %4, align 8, !dbg !1615
  call void @_ZN7__ubsanL26handleFunctionTypeMismatchEP24FunctionTypeMismatchDatam(ptr noundef %5, i64 noundef %6), !dbg !1616
  ret void, !dbg !1617
}

; Function Attrs: noreturn nounwind
declare void @abort() #7

; Function Attrs: noinline nounwind sspstrong uwtable
define void @klee_overshift_check(i64 noundef %0, i64 noundef %1) #0 !dbg !1618 {
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  store i64 %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1622, !DIExpression(), !1623)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1624, !DIExpression(), !1625)
  %5 = load i64, ptr %4, align 8, !dbg !1626
  %6 = load i64, ptr %3, align 8, !dbg !1628
  %7 = icmp uge i64 %5, %6, !dbg !1629
  br i1 %7, label %8, label %9, !dbg !1630

8:                                                ; preds = %2
  call void @klee_report_error(ptr noundef @.str.57, i32 noundef 0, ptr noundef @.str.1.58, ptr noundef @.str.2.59) #8, !dbg !1631
  unreachable, !dbg !1631

9:                                                ; preds = %2
  ret void, !dbg !1633
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
!641 = !DICompositeType(tag: DW_TAG_array_type, baseType: !251, size: 1120, elements: !118)
!642 = !DILocation(line: 19, column: 14, scope: !637)
!643 = !DILocalVariable(name: "data", scope: !637, file: !2, line: 20, type: !644)
!644 = !DICompositeType(tag: DW_TAG_array_type, baseType: !251, size: 512, elements: !205)
!645 = !DILocation(line: 20, column: 14, scope: !637)
!646 = !DILocalVariable(name: "permutation", scope: !637, file: !2, line: 20, type: !644)
!647 = !DILocation(line: 20, column: 30, scope: !637)
!648 = !DILocalVariable(name: "target", scope: !637, file: !2, line: 21, type: !644)
!649 = !DILocation(line: 21, column: 14, scope: !637)
!650 = !DILocalVariable(name: "used", scope: !637, file: !2, line: 21, type: !644)
!651 = !DILocation(line: 21, column: 32, scope: !637)
!652 = !DILocalVariable(name: "trace", scope: !637, file: !2, line: 21, type: !653)
!653 = !DICompositeType(tag: DW_TAG_array_type, baseType: !251, size: 1024, elements: !654)
!654 = !{!655}
!655 = !DISubrange(count: 32)
!656 = !DILocation(line: 21, column: 48, scope: !637)
!657 = !DILocalVariable(name: "out", scope: !637, file: !2, line: 21, type: !658)
!658 = !DICompositeType(tag: DW_TAG_array_type, baseType: !251, size: 96, elements: !659)
!659 = !{!660}
!660 = !DISubrange(count: 3)
!661 = !DILocation(line: 21, column: 70, scope: !637)
!662 = !DILocation(line: 22, column: 24, scope: !637)
!663 = !DILocation(line: 22, column: 5, scope: !637)
!664 = !DILocalVariable(name: "valid", scope: !637, file: !2, line: 23, type: !251)
!665 = !DILocation(line: 23, column: 14, scope: !637)
!666 = !DILocalVariable(name: "i", scope: !667, file: !2, line: 24, type: !251)
!667 = distinct !DILexicalBlock(scope: !637, file: !2, line: 24, column: 5)
!668 = !DILocation(line: 24, column: 19, scope: !667)
!669 = !DILocation(line: 24, column: 10, scope: !667)
!670 = !DILocation(line: 24, column: 26, scope: !671)
!671 = distinct !DILexicalBlock(scope: !667, file: !2, line: 24, column: 5)
!672 = !DILocation(line: 24, column: 28, scope: !671)
!673 = !DILocation(line: 24, column: 5, scope: !667)
!674 = !DILocation(line: 25, column: 24, scope: !675)
!675 = distinct !DILexicalBlock(scope: !671, file: !2, line: 24, column: 45)
!676 = !DILocation(line: 25, column: 18, scope: !675)
!677 = !{!"branch_weights", i32 1048575, i32 1}
!678 = !DILocation(line: 25, column: 27, scope: !675)
!679 = !DILocation(line: 25, column: 15, scope: !675)
!680 = !DILocalVariable(name: "j", scope: !681, file: !2, line: 26, type: !251)
!681 = distinct !DILexicalBlock(scope: !675, file: !2, line: 26, column: 9)
!682 = !DILocation(line: 26, column: 23, scope: !681)
!683 = !DILocation(line: 26, column: 14, scope: !681)
!684 = !DILocation(line: 26, column: 30, scope: !685)
!685 = distinct !DILexicalBlock(scope: !681, file: !2, line: 26, column: 9)
!686 = !DILocation(line: 26, column: 34, scope: !685)
!687 = !DILocation(line: 26, column: 32, scope: !685)
!688 = !DILocation(line: 26, column: 9, scope: !681)
!689 = !DILocation(line: 27, column: 28, scope: !685)
!690 = !DILocation(line: 27, column: 22, scope: !685)
!691 = !DILocation(line: 27, column: 40, scope: !685)
!692 = !DILocation(line: 27, column: 34, scope: !685)
!693 = !DILocation(line: 27, column: 31, scope: !685)
!694 = !DILocation(line: 27, column: 19, scope: !685)
!695 = !DILocation(line: 26, column: 37, scope: !685)
!696 = !DILocation(line: 26, column: 9, scope: !685)
!697 = distinct !{!697, !688, !698, !699}
!698 = !DILocation(line: 27, column: 41, scope: !681)
!699 = !{!"llvm.loop.mustprogress"}
!700 = !DILocation(line: 28, column: 32, scope: !675)
!701 = !DILocation(line: 28, column: 26, scope: !675)
!702 = !DILocation(line: 28, column: 21, scope: !675)
!703 = !DILocation(line: 28, column: 24, scope: !675)
!704 = !DILocation(line: 29, column: 36, scope: !675)
!705 = !DILocation(line: 29, column: 34, scope: !675)
!706 = !DILocation(line: 29, column: 19, scope: !675)
!707 = !DILocation(line: 29, column: 14, scope: !675)
!708 = !DILocation(line: 29, column: 17, scope: !675)
!709 = !DILocation(line: 24, column: 40, scope: !671)
!710 = !DILocation(line: 24, column: 5, scope: !671)
!711 = distinct !{!711, !673, !712, !699}
!712 = !DILocation(line: 30, column: 5, scope: !667)
!713 = !DILocation(line: 33, column: 17, scope: !637)
!714 = !DILocation(line: 33, column: 23, scope: !637)
!715 = !DILocation(line: 33, column: 5, scope: !637)
!716 = !DILocalVariable(name: "i", scope: !717, file: !2, line: 34, type: !251)
!717 = distinct !DILexicalBlock(scope: !637, file: !2, line: 34, column: 5)
!718 = !DILocation(line: 34, column: 19, scope: !717)
!719 = !DILocation(line: 34, column: 10, scope: !717)
!720 = !DILocation(line: 34, column: 26, scope: !721)
!721 = distinct !DILexicalBlock(scope: !717, file: !2, line: 34, column: 5)
!722 = !DILocation(line: 34, column: 28, scope: !721)
!723 = !DILocation(line: 34, column: 5, scope: !717)
!724 = !DILocation(line: 35, column: 40, scope: !721)
!725 = !DILocation(line: 35, column: 38, scope: !721)
!726 = !DILocation(line: 35, column: 18, scope: !721)
!727 = !DILocation(line: 35, column: 13, scope: !721)
!728 = !DILocation(line: 35, column: 16, scope: !721)
!729 = !DILocation(line: 34, column: 34, scope: !721)
!730 = !DILocation(line: 34, column: 5, scope: !721)
!731 = distinct !{!731, !723, !732, !699}
!732 = !DILocation(line: 35, column: 41, scope: !717)
!733 = !DILocalVariable(name: "status", scope: !637, file: !2, line: 36, type: !251)
!734 = !DILocation(line: 36, column: 14, scope: !637)
!735 = !DILocation(line: 36, column: 41, scope: !637)
!736 = !DILocation(line: 36, column: 47, scope: !637)
!737 = !DILocation(line: 36, column: 60, scope: !637)
!738 = !DILocation(line: 36, column: 68, scope: !637)
!739 = !DILocation(line: 36, column: 74, scope: !637)
!740 = !DILocation(line: 36, column: 81, scope: !637)
!741 = !DILocation(line: 36, column: 23, scope: !637)
!742 = !DILocation(line: 37, column: 5, scope: !637)
!743 = !DILocalVariable(name: "i", scope: !744, file: !2, line: 38, type: !251)
!744 = distinct !DILexicalBlock(scope: !637, file: !2, line: 38, column: 5)
!745 = !DILocation(line: 38, column: 19, scope: !744)
!746 = !DILocation(line: 38, column: 10, scope: !744)
!747 = !DILocation(line: 38, column: 26, scope: !748)
!748 = distinct !DILexicalBlock(scope: !744, file: !2, line: 38, column: 5)
!749 = !DILocation(line: 38, column: 28, scope: !748)
!750 = !DILocation(line: 38, column: 5, scope: !744)
!751 = !DILocation(line: 39, column: 9, scope: !752)
!752 = distinct !DILexicalBlock(scope: !748, file: !2, line: 38, column: 45)
!753 = !DILocation(line: 40, column: 9, scope: !752)
!754 = !DILocation(line: 38, column: 40, scope: !748)
!755 = !DILocation(line: 38, column: 5, scope: !748)
!756 = distinct !{!756, !750, !757, !699}
!757 = !DILocation(line: 41, column: 5, scope: !744)
!758 = !DILocalVariable(name: "i", scope: !759, file: !2, line: 43, type: !251)
!759 = distinct !DILexicalBlock(scope: !637, file: !2, line: 43, column: 5)
!760 = !DILocation(line: 43, column: 19, scope: !759)
!761 = !DILocation(line: 43, column: 10, scope: !759)
!762 = !DILocation(line: 43, column: 26, scope: !763)
!763 = distinct !DILexicalBlock(scope: !759, file: !2, line: 43, column: 5)
!764 = !DILocation(line: 43, column: 28, scope: !763)
!765 = !DILocation(line: 43, column: 5, scope: !759)
!766 = !DILocation(line: 44, column: 9, scope: !763)
!767 = !DILocation(line: 43, column: 34, scope: !763)
!768 = !DILocation(line: 43, column: 5, scope: !763)
!769 = distinct !{!769, !765, !770, !699}
!770 = !DILocation(line: 44, column: 9, scope: !759)
!771 = !DILocation(line: 45, column: 5, scope: !637)
!772 = distinct !DISubprogram(name: "main", scope: !32, file: !32, line: 6, type: !638, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !215, retainedNodes: !334)
!773 = !DILocalVariable(name: "result", scope: !772, file: !32, line: 8, type: !258)
!774 = !DILocation(line: 8, column: 9, scope: !772)
!775 = !DILocation(line: 8, column: 18, scope: !772)
!776 = !DILocalVariable(name: "completed", scope: !772, file: !32, line: 9, type: !777)
!777 = !DIBasicType(name: "unsigned char", size: 8, encoding: DW_ATE_unsigned_char)
!778 = !DILocation(line: 9, column: 19, scope: !772)
!779 = !DILocation(line: 11, column: 5, scope: !772)
!780 = !DILocation(line: 12, column: 12, scope: !772)
!781 = !DILocation(line: 12, column: 5, scope: !772)
!782 = distinct !DISubprogram(name: "__ubsan_handle_type_mismatch_v1", scope: !38, file: !38, line: 174, type: !783, scopeLine: 175, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!783 = !DISubroutineType(types: !784)
!784 = !{null, !785, !794}
!785 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !786, size: 64)
!786 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "TypeMismatchData", file: !317, line: 25, size: 256, flags: DIFlagTypePassByValue | DIFlagNonTrivial, elements: !787, identifier: "_ZTS16TypeMismatchData")
!787 = !{!788, !790, !792, !793}
!788 = !DIDerivedType(tag: DW_TAG_member, name: "Loc", scope: !786, file: !317, line: 26, baseType: !789, size: 128)
!789 = !DICompositeType(tag: DW_TAG_class_type, name: "SourceLocation", scope: !224, file: !222, line: 28, size: 128, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTSN7__ubsan14SourceLocationE")
!790 = !DIDerivedType(tag: DW_TAG_member, name: "Type", scope: !786, file: !317, line: 27, baseType: !791, size: 64, offset: 128)
!791 = !DIDerivedType(tag: DW_TAG_reference_type, baseType: !241, size: 64)
!792 = !DIDerivedType(tag: DW_TAG_member, name: "LogAlignment", scope: !786, file: !317, line: 28, baseType: !777, size: 8, offset: 192)
!793 = !DIDerivedType(tag: DW_TAG_member, name: "TypeCheckKind", scope: !786, file: !317, line: 29, baseType: !777, size: 8, offset: 200)
!794 = !DIDerivedType(tag: DW_TAG_typedef, name: "ValueHandle", scope: !224, file: !222, line: 78, baseType: !311)
!795 = !DILocalVariable(name: "Data", arg: 1, scope: !782, file: !38, line: 174, type: !785)
!796 = !DILocation(line: 174, column: 67, scope: !782)
!797 = !DILocalVariable(name: "Pointer", arg: 2, scope: !782, file: !38, line: 175, type: !794)
!798 = !DILocation(line: 175, column: 61, scope: !782)
!799 = !DILocation(line: 177, column: 26, scope: !782)
!800 = !DILocation(line: 177, column: 32, scope: !782)
!801 = !DILocation(line: 177, column: 3, scope: !782)
!802 = !DILocation(line: 178, column: 1, scope: !782)
!803 = distinct !DISubprogram(name: "handleTypeMismatchImpl", linkageName: "_ZN7__ubsanL22handleTypeMismatchImplEP16TypeMismatchDatam", scope: !224, file: !38, line: 158, type: !783, scopeLine: 159, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!804 = !DILocalVariable(name: "Data", arg: 1, scope: !803, file: !38, line: 158, type: !785)
!805 = !DILocation(line: 158, column: 54, scope: !803)
!806 = !DILocalVariable(name: "Pointer", arg: 2, scope: !803, file: !38, line: 159, type: !794)
!807 = !DILocation(line: 159, column: 48, scope: !803)
!808 = !DILocalVariable(name: "Alignment", scope: !803, file: !38, line: 160, type: !311)
!809 = !DILocation(line: 160, column: 8, scope: !803)
!810 = !DILocation(line: 160, column: 31, scope: !803)
!811 = !DILocation(line: 160, column: 37, scope: !803)
!812 = !DILocation(line: 160, column: 28, scope: !803)
!813 = !{!"True"}
!814 = !DILocalVariable(name: "ET", scope: !803, file: !38, line: 161, type: !256)
!815 = !DILocation(line: 161, column: 13, scope: !803)
!816 = !DILocation(line: 162, column: 8, scope: !817)
!817 = distinct !DILexicalBlock(scope: !803, file: !38, line: 162, column: 7)
!818 = !DILocation(line: 162, column: 7, scope: !803)
!819 = !DILocation(line: 163, column: 11, scope: !817)
!820 = !DILocation(line: 163, column: 17, scope: !817)
!821 = !DILocation(line: 163, column: 31, scope: !817)
!822 = !DILocation(line: 163, column: 10, scope: !817)
!823 = !DILocation(line: 163, column: 8, scope: !817)
!824 = !DILocation(line: 163, column: 5, scope: !817)
!825 = !DILocation(line: 166, column: 12, scope: !826)
!826 = distinct !DILexicalBlock(scope: !817, file: !38, line: 166, column: 12)
!827 = !DILocation(line: 166, column: 23, scope: !826)
!828 = !DILocation(line: 166, column: 33, scope: !826)
!829 = !DILocation(line: 166, column: 20, scope: !826)
!830 = !DILocation(line: 166, column: 12, scope: !817)
!831 = !DILocation(line: 167, column: 8, scope: !826)
!832 = !DILocation(line: 167, column: 5, scope: !826)
!833 = !DILocation(line: 169, column: 8, scope: !826)
!834 = !DILocation(line: 171, column: 21, scope: !803)
!835 = !DILocation(line: 171, column: 3, scope: !803)
!836 = distinct !DISubprogram(name: "report_error_type", linkageName: "_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE", scope: !224, file: !38, line: 115, type: !837, scopeLine: 115, flags: DIFlagPrototyped | DIFlagNoReturn, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!837 = !DISubroutineType(types: !838)
!838 = !{null, !256}
!839 = !DILocalVariable(name: "ET", arg: 1, scope: !836, file: !38, line: 115, type: !256)
!840 = !DILocation(line: 115, column: 67, scope: !836)
!841 = !DILocation(line: 116, column: 36, scope: !836)
!842 = !DILocation(line: 116, column: 16, scope: !836)
!843 = !DILocation(line: 116, column: 52, scope: !836)
!844 = !DILocation(line: 116, column: 41, scope: !836)
!845 = !DILocation(line: 116, column: 3, scope: !836)
!846 = distinct !DISubprogram(name: "ConvertTypeToString", linkageName: "_ZN7__ubsanL19ConvertTypeToStringENS_9ErrorTypeE", scope: !224, file: !38, line: 25, type: !847, scopeLine: 25, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!847 = !DISubroutineType(types: !848)
!848 = !{!239, !256}
!849 = !DILocalVariable(name: "Type", arg: 1, scope: !846, file: !38, line: 25, type: !256)
!850 = !DILocation(line: 25, column: 50, scope: !846)
!851 = !DILocation(line: 26, column: 11, scope: !846)
!852 = !DILocation(line: 26, column: 3, scope: !846)
!853 = !DILocation(line: 27, column: 1, scope: !854)
!854 = !DILexicalBlockFile(scope: !855, file: !53, discriminator: 0)
!855 = distinct !DILexicalBlock(scope: !846, file: !38, line: 26, column: 17)
!856 = !DILocation(line: 28, column: 1, scope: !854)
!857 = !DILocation(line: 29, column: 1, scope: !854)
!858 = !DILocation(line: 31, column: 1, scope: !854)
!859 = !DILocation(line: 32, column: 1, scope: !854)
!860 = !DILocation(line: 34, column: 1, scope: !854)
!861 = !DILocation(line: 36, column: 1, scope: !854)
!862 = !DILocation(line: 37, column: 1, scope: !854)
!863 = !DILocation(line: 38, column: 1, scope: !854)
!864 = !DILocation(line: 39, column: 1, scope: !854)
!865 = !DILocation(line: 40, column: 1, scope: !854)
!866 = !DILocation(line: 42, column: 1, scope: !854)
!867 = !DILocation(line: 44, column: 1, scope: !854)
!868 = !DILocation(line: 46, column: 1, scope: !854)
!869 = !DILocation(line: 47, column: 1, scope: !854)
!870 = !DILocation(line: 48, column: 1, scope: !854)
!871 = !DILocation(line: 49, column: 1, scope: !854)
!872 = !DILocation(line: 52, column: 1, scope: !854)
!873 = !DILocation(line: 55, column: 1, scope: !854)
!874 = !DILocation(line: 58, column: 1, scope: !854)
!875 = !DILocation(line: 61, column: 1, scope: !854)
!876 = !DILocation(line: 62, column: 1, scope: !854)
!877 = !DILocation(line: 63, column: 1, scope: !854)
!878 = !DILocation(line: 64, column: 1, scope: !854)
!879 = !DILocation(line: 65, column: 1, scope: !854)
!880 = !DILocation(line: 66, column: 1, scope: !854)
!881 = !DILocation(line: 67, column: 1, scope: !854)
!882 = !DILocation(line: 68, column: 1, scope: !854)
!883 = !DILocation(line: 69, column: 1, scope: !854)
!884 = !DILocation(line: 70, column: 1, scope: !854)
!885 = !DILocation(line: 71, column: 1, scope: !854)
!886 = !DILocation(line: 73, column: 1, scope: !854)
!887 = !DILocation(line: 75, column: 1, scope: !854)
!888 = !DILocation(line: 76, column: 1, scope: !854)
!889 = !DILocation(line: 78, column: 1, scope: !854)
!890 = !DILocation(line: 79, column: 1, scope: !854)
!891 = !DILocation(line: 32, column: 3, scope: !892)
!892 = !DILexicalBlockFile(scope: !855, file: !38, discriminator: 0)
!893 = !DILocation(line: 33, column: 1, scope: !846)
!894 = distinct !DISubprogram(name: "get_suffix", linkageName: "_ZN7__ubsanL10get_suffixENS_9ErrorTypeE", scope: !224, file: !38, line: 40, type: !847, scopeLine: 40, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!895 = !DILocalVariable(name: "ET", arg: 1, scope: !894, file: !38, line: 40, type: !256)
!896 = !DILocation(line: 40, column: 41, scope: !894)
!897 = !DILocation(line: 41, column: 11, scope: !894)
!898 = !DILocation(line: 41, column: 3, scope: !894)
!899 = !DILocation(line: 46, column: 5, scope: !900)
!900 = distinct !DILexicalBlock(scope: !894, file: !38, line: 41, column: 15)
!901 = !DILocation(line: 55, column: 5, scope: !900)
!902 = !DILocation(line: 59, column: 5, scope: !900)
!903 = !DILocation(line: 62, column: 5, scope: !900)
!904 = !DILocation(line: 65, column: 5, scope: !900)
!905 = !DILocation(line: 67, column: 5, scope: !900)
!906 = !DILocation(line: 71, column: 5, scope: !900)
!907 = !DILocation(line: 74, column: 5, scope: !900)
!908 = !DILocation(line: 77, column: 5, scope: !900)
!909 = !DILocation(line: 80, column: 5, scope: !900)
!910 = !DILocation(line: 82, column: 5, scope: !900)
!911 = !DILocation(line: 84, column: 5, scope: !900)
!912 = !DILocation(line: 86, column: 5, scope: !900)
!913 = !DILocation(line: 88, column: 5, scope: !900)
!914 = !DILocation(line: 90, column: 5, scope: !900)
!915 = !DILocation(line: 93, column: 5, scope: !900)
!916 = !DILocation(line: 96, column: 5, scope: !900)
!917 = !DILocation(line: 105, column: 5, scope: !900)
!918 = !DILocation(line: 109, column: 5, scope: !900)
!919 = !DILocation(line: 112, column: 5, scope: !900)
!920 = !DILocation(line: 114, column: 1, scope: !894)
!921 = distinct !DISubprogram(name: "report_error", linkageName: "_ZN7__ubsanL12report_errorEPKcS1_", scope: !224, file: !38, line: 35, type: !922, scopeLine: 36, flags: DIFlagPrototyped | DIFlagNoReturn, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!922 = !DISubroutineType(types: !923)
!923 = !{null, !239, !239}
!924 = !DILocalVariable(name: "msg", arg: 1, scope: !921, file: !38, line: 35, type: !239)
!925 = !DILocation(line: 35, column: 64, scope: !921)
!926 = !DILocalVariable(name: "suffix", arg: 2, scope: !921, file: !38, line: 36, type: !239)
!927 = !DILocation(line: 36, column: 64, scope: !921)
!928 = !DILocation(line: 37, column: 41, scope: !921)
!929 = !DILocation(line: 37, column: 46, scope: !921)
!930 = !DILocation(line: 37, column: 3, scope: !921)
!931 = distinct !DISubprogram(name: "__ubsan_handle_type_mismatch_v1_abort", scope: !38, file: !38, line: 180, type: !783, scopeLine: 181, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!932 = !DILocalVariable(name: "Data", arg: 1, scope: !931, file: !38, line: 180, type: !785)
!933 = !DILocation(line: 180, column: 73, scope: !931)
!934 = !DILocalVariable(name: "Pointer", arg: 2, scope: !931, file: !38, line: 181, type: !794)
!935 = !DILocation(line: 181, column: 67, scope: !931)
!936 = !DILocation(line: 183, column: 26, scope: !931)
!937 = !DILocation(line: 183, column: 32, scope: !931)
!938 = !DILocation(line: 183, column: 3, scope: !931)
!939 = !DILocation(line: 184, column: 1, scope: !931)
!940 = distinct !DISubprogram(name: "__ubsan_handle_alignment_assumption", scope: !38, file: !38, line: 195, type: !941, scopeLine: 197, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!941 = !DISubroutineType(types: !942)
!942 = !{null, !943, !794, !794, !794}
!943 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !944, size: 64)
!944 = !DICompositeType(tag: DW_TAG_structure_type, name: "AlignmentAssumptionData", file: !317, line: 32, size: 320, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS23AlignmentAssumptionData")
!945 = !DILocalVariable(name: "Data", arg: 1, scope: !940, file: !38, line: 195, type: !943)
!946 = !DILocation(line: 195, column: 62, scope: !940)
!947 = !DILocalVariable(name: "Pointer", arg: 2, scope: !940, file: !38, line: 196, type: !794)
!948 = !DILocation(line: 196, column: 49, scope: !940)
!949 = !DILocalVariable(name: "Alignment", arg: 3, scope: !940, file: !38, line: 196, type: !794)
!950 = !DILocation(line: 196, column: 70, scope: !940)
!951 = !DILocalVariable(name: "Offset", arg: 4, scope: !940, file: !38, line: 197, type: !794)
!952 = !DILocation(line: 197, column: 49, scope: !940)
!953 = !DILocation(line: 198, column: 33, scope: !940)
!954 = !DILocation(line: 198, column: 39, scope: !940)
!955 = !DILocation(line: 198, column: 48, scope: !940)
!956 = !DILocation(line: 198, column: 59, scope: !940)
!957 = !DILocation(line: 198, column: 3, scope: !940)
!958 = !DILocation(line: 199, column: 1, scope: !940)
!959 = distinct !DISubprogram(name: "handleAlignmentAssumptionImpl", linkageName: "_ZN7__ubsanL29handleAlignmentAssumptionImplEP23AlignmentAssumptionDatammm", scope: !224, file: !38, line: 186, type: !941, scopeLine: 189, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!960 = !DILocalVariable(arg: 1, scope: !959, file: !38, line: 186, type: !943)
!961 = !DILocation(line: 186, column: 77, scope: !959)
!962 = !DILocalVariable(arg: 2, scope: !959, file: !38, line: 187, type: !794)
!963 = !DILocation(line: 187, column: 66, scope: !959)
!964 = !DILocalVariable(arg: 3, scope: !959, file: !38, line: 188, type: !794)
!965 = !DILocation(line: 188, column: 68, scope: !959)
!966 = !DILocalVariable(arg: 4, scope: !959, file: !38, line: 189, type: !794)
!967 = !DILocation(line: 189, column: 65, scope: !959)
!968 = !DILocalVariable(name: "ET", scope: !959, file: !38, line: 190, type: !256)
!969 = !DILocation(line: 190, column: 13, scope: !959)
!970 = !DILocation(line: 191, column: 21, scope: !959)
!971 = !DILocation(line: 191, column: 3, scope: !959)
!972 = distinct !DISubprogram(name: "__ubsan_handle_alignment_assumption_abort", scope: !38, file: !38, line: 201, type: !941, scopeLine: 203, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!973 = !DILocalVariable(name: "Data", arg: 1, scope: !972, file: !38, line: 202, type: !943)
!974 = !DILocation(line: 202, column: 30, scope: !972)
!975 = !DILocalVariable(name: "Pointer", arg: 2, scope: !972, file: !38, line: 202, type: !794)
!976 = !DILocation(line: 202, column: 48, scope: !972)
!977 = !DILocalVariable(name: "Alignment", arg: 3, scope: !972, file: !38, line: 202, type: !794)
!978 = !DILocation(line: 202, column: 69, scope: !972)
!979 = !DILocalVariable(name: "Offset", arg: 4, scope: !972, file: !38, line: 203, type: !794)
!980 = !DILocation(line: 203, column: 17, scope: !972)
!981 = !DILocation(line: 204, column: 33, scope: !972)
!982 = !DILocation(line: 204, column: 39, scope: !972)
!983 = !DILocation(line: 204, column: 48, scope: !972)
!984 = !DILocation(line: 204, column: 59, scope: !972)
!985 = !DILocation(line: 204, column: 3, scope: !972)
!986 = !DILocation(line: 205, column: 1, scope: !972)
!987 = distinct !DISubprogram(name: "__ubsan_handle_add_overflow", scope: !38, file: !38, line: 222, type: !988, scopeLine: 222, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!988 = !DISubroutineType(types: !989)
!989 = !{null, !990, !794, !794}
!990 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !991, size: 64)
!991 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "OverflowData", file: !317, line: 38, size: 192, flags: DIFlagTypePassByValue | DIFlagNonTrivial, elements: !992, identifier: "_ZTS12OverflowData")
!992 = !{!993, !994}
!993 = !DIDerivedType(tag: DW_TAG_member, name: "Loc", scope: !991, file: !317, line: 39, baseType: !789, size: 128)
!994 = !DIDerivedType(tag: DW_TAG_member, name: "Type", scope: !991, file: !317, line: 40, baseType: !791, size: 64, offset: 128)
!995 = !DILocalVariable(name: "Data", arg: 1, scope: !987, file: !38, line: 222, type: !990)
!996 = !DILocation(line: 222, column: 1, scope: !987)
!997 = !DILocalVariable(name: "LHS", arg: 2, scope: !987, file: !38, line: 222, type: !794)
!998 = !DILocalVariable(name: "RHS", arg: 3, scope: !987, file: !38, line: 222, type: !794)
!999 = distinct !DISubprogram(name: "handleIntegerOverflowImpl", linkageName: "_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc", scope: !224, file: !38, line: 208, type: !1000, scopeLine: 209, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1000 = !DISubroutineType(types: !1001)
!1001 = !{null, !990, !794, !239}
!1002 = !DILocalVariable(name: "Data", arg: 1, scope: !999, file: !38, line: 208, type: !990)
!1003 = !DILocation(line: 208, column: 53, scope: !999)
!1004 = !DILocalVariable(arg: 2, scope: !999, file: !38, line: 208, type: !794)
!1005 = !DILocation(line: 208, column: 78, scope: !999)
!1006 = !DILocalVariable(arg: 3, scope: !999, file: !38, line: 209, type: !239)
!1007 = !DILocation(line: 209, column: 64, scope: !999)
!1008 = !DILocalVariable(name: "IsSigned", scope: !999, file: !38, line: 210, type: !248)
!1009 = !DILocation(line: 210, column: 8, scope: !999)
!1010 = !DILocation(line: 210, column: 19, scope: !999)
!1011 = !DILocation(line: 210, column: 25, scope: !999)
!1012 = !DILocation(line: 210, column: 30, scope: !999)
!1013 = !DILocalVariable(name: "ET", scope: !999, file: !38, line: 211, type: !256)
!1014 = !DILocation(line: 211, column: 13, scope: !999)
!1015 = !DILocation(line: 211, column: 18, scope: !999)
!1016 = !DILocation(line: 213, column: 21, scope: !999)
!1017 = !DILocation(line: 213, column: 3, scope: !999)
!1018 = distinct !DISubprogram(name: "isSignedIntegerTy", linkageName: "_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv", scope: !223, file: !222, line: 73, type: !246, scopeLine: 73, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, declaration: !249, retainedNodes: !334)
!1019 = !DILocalVariable(name: "this", arg: 1, scope: !1018, type: !1020, flags: DIFlagArtificial | DIFlagObjectPointer)
!1020 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !241, size: 64)
!1021 = !DILocation(line: 0, scope: !1018)
!1022 = !DILocation(line: 73, column: 43, scope: !1018)
!1023 = !DILocation(line: 73, column: 57, scope: !1018)
!1024 = !DILocation(line: 73, column: 61, scope: !1018)
!1025 = !DILocation(line: 73, column: 70, scope: !1018)
!1026 = !DILocation(line: 73, column: 60, scope: !1018)
!1027 = !DILocation(line: 73, column: 36, scope: !1018)
!1028 = distinct !DISubprogram(name: "isIntegerTy", linkageName: "_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv", scope: !223, file: !222, line: 72, type: !246, scopeLine: 72, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, declaration: !245, retainedNodes: !334)
!1029 = !DILocalVariable(name: "this", arg: 1, scope: !1028, type: !1020, flags: DIFlagArtificial | DIFlagObjectPointer)
!1030 = !DILocation(line: 0, scope: !1028)
!1031 = !DILocation(line: 72, column: 37, scope: !1028)
!1032 = !DILocation(line: 72, column: 47, scope: !1028)
!1033 = !DILocation(line: 72, column: 30, scope: !1028)
!1034 = distinct !DISubprogram(name: "getKind", linkageName: "_ZNK7__ubsan14TypeDescriptor7getKindEv", scope: !223, file: !222, line: 70, type: !243, scopeLine: 70, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, declaration: !242, retainedNodes: !334)
!1035 = !DILocalVariable(name: "this", arg: 1, scope: !1034, type: !1020, flags: DIFlagArtificial | DIFlagObjectPointer)
!1036 = !DILocation(line: 0, scope: !1034)
!1037 = !DILocation(line: 70, column: 51, scope: !1034)
!1038 = !DILocation(line: 70, column: 33, scope: !1034)
!1039 = !DILocation(line: 70, column: 26, scope: !1034)
!1040 = distinct !DISubprogram(name: "__ubsan_handle_add_overflow_abort", scope: !38, file: !38, line: 223, type: !988, scopeLine: 223, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1041 = !DILocalVariable(name: "Data", arg: 1, scope: !1040, file: !38, line: 223, type: !990)
!1042 = !DILocation(line: 223, column: 1, scope: !1040)
!1043 = !DILocalVariable(name: "LHS", arg: 2, scope: !1040, file: !38, line: 223, type: !794)
!1044 = !DILocalVariable(name: "RHS", arg: 3, scope: !1040, file: !38, line: 223, type: !794)
!1045 = distinct !DISubprogram(name: "__ubsan_handle_sub_overflow", scope: !38, file: !38, line: 224, type: !988, scopeLine: 224, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1046 = !DILocalVariable(name: "Data", arg: 1, scope: !1045, file: !38, line: 224, type: !990)
!1047 = !DILocation(line: 224, column: 1, scope: !1045)
!1048 = !DILocalVariable(name: "LHS", arg: 2, scope: !1045, file: !38, line: 224, type: !794)
!1049 = !DILocalVariable(name: "RHS", arg: 3, scope: !1045, file: !38, line: 224, type: !794)
!1050 = distinct !DISubprogram(name: "__ubsan_handle_sub_overflow_abort", scope: !38, file: !38, line: 225, type: !988, scopeLine: 225, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1051 = !DILocalVariable(name: "Data", arg: 1, scope: !1050, file: !38, line: 225, type: !990)
!1052 = !DILocation(line: 225, column: 1, scope: !1050)
!1053 = !DILocalVariable(name: "LHS", arg: 2, scope: !1050, file: !38, line: 225, type: !794)
!1054 = !DILocalVariable(name: "RHS", arg: 3, scope: !1050, file: !38, line: 225, type: !794)
!1055 = distinct !DISubprogram(name: "__ubsan_handle_mul_overflow", scope: !38, file: !38, line: 226, type: !988, scopeLine: 226, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1056 = !DILocalVariable(name: "Data", arg: 1, scope: !1055, file: !38, line: 226, type: !990)
!1057 = !DILocation(line: 226, column: 1, scope: !1055)
!1058 = !DILocalVariable(name: "LHS", arg: 2, scope: !1055, file: !38, line: 226, type: !794)
!1059 = !DILocalVariable(name: "RHS", arg: 3, scope: !1055, file: !38, line: 226, type: !794)
!1060 = distinct !DISubprogram(name: "__ubsan_handle_mul_overflow_abort", scope: !38, file: !38, line: 227, type: !988, scopeLine: 227, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1061 = !DILocalVariable(name: "Data", arg: 1, scope: !1060, file: !38, line: 227, type: !990)
!1062 = !DILocation(line: 227, column: 1, scope: !1060)
!1063 = !DILocalVariable(name: "LHS", arg: 2, scope: !1060, file: !38, line: 227, type: !794)
!1064 = !DILocalVariable(name: "RHS", arg: 3, scope: !1060, file: !38, line: 227, type: !794)
!1065 = distinct !DISubprogram(name: "__ubsan_handle_negate_overflow", scope: !38, file: !38, line: 237, type: !1066, scopeLine: 238, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1066 = !DISubroutineType(types: !1067)
!1067 = !{null, !990, !794}
!1068 = !DILocalVariable(name: "Data", arg: 1, scope: !1065, file: !38, line: 237, type: !990)
!1069 = !DILocation(line: 237, column: 62, scope: !1065)
!1070 = !DILocalVariable(name: "OldVal", arg: 2, scope: !1065, file: !38, line: 238, type: !794)
!1071 = !DILocation(line: 238, column: 60, scope: !1065)
!1072 = !DILocation(line: 239, column: 28, scope: !1065)
!1073 = !DILocation(line: 239, column: 34, scope: !1065)
!1074 = !DILocation(line: 239, column: 3, scope: !1065)
!1075 = !DILocation(line: 240, column: 1, scope: !1065)
!1076 = distinct !DISubprogram(name: "handleNegateOverflowImpl", linkageName: "_ZN7__ubsanL24handleNegateOverflowImplEP12OverflowDatam", scope: !224, file: !38, line: 229, type: !1066, scopeLine: 230, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1077 = !DILocalVariable(name: "Data", arg: 1, scope: !1076, file: !38, line: 229, type: !990)
!1078 = !DILocation(line: 229, column: 52, scope: !1076)
!1079 = !DILocalVariable(arg: 2, scope: !1076, file: !38, line: 230, type: !794)
!1080 = !DILocation(line: 230, column: 60, scope: !1076)
!1081 = !DILocalVariable(name: "IsSigned", scope: !1076, file: !38, line: 231, type: !248)
!1082 = !DILocation(line: 231, column: 8, scope: !1076)
!1083 = !DILocation(line: 231, column: 19, scope: !1076)
!1084 = !DILocation(line: 231, column: 25, scope: !1076)
!1085 = !DILocation(line: 231, column: 30, scope: !1076)
!1086 = !DILocalVariable(name: "ET", scope: !1076, file: !38, line: 232, type: !256)
!1087 = !DILocation(line: 232, column: 13, scope: !1076)
!1088 = !DILocation(line: 232, column: 18, scope: !1076)
!1089 = !DILocation(line: 234, column: 21, scope: !1076)
!1090 = !DILocation(line: 234, column: 3, scope: !1076)
!1091 = distinct !DISubprogram(name: "__ubsan_handle_negate_overflow_abort", scope: !38, file: !38, line: 242, type: !1066, scopeLine: 243, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1092 = !DILocalVariable(name: "Data", arg: 1, scope: !1091, file: !38, line: 242, type: !990)
!1093 = !DILocation(line: 242, column: 68, scope: !1091)
!1094 = !DILocalVariable(name: "OldVal", arg: 2, scope: !1091, file: !38, line: 243, type: !794)
!1095 = !DILocation(line: 243, column: 66, scope: !1091)
!1096 = !DILocation(line: 244, column: 28, scope: !1091)
!1097 = !DILocation(line: 244, column: 34, scope: !1091)
!1098 = !DILocation(line: 244, column: 3, scope: !1091)
!1099 = !DILocation(line: 245, column: 1, scope: !1091)
!1100 = distinct !DISubprogram(name: "__ubsan_handle_divrem_overflow", scope: !38, file: !38, line: 257, type: !988, scopeLine: 259, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1101 = !DILocalVariable(name: "Data", arg: 1, scope: !1100, file: !38, line: 257, type: !990)
!1102 = !DILocation(line: 257, column: 62, scope: !1100)
!1103 = !DILocalVariable(name: "LHS", arg: 2, scope: !1100, file: !38, line: 258, type: !794)
!1104 = !DILocation(line: 258, column: 60, scope: !1100)
!1105 = !DILocalVariable(name: "RHS", arg: 3, scope: !1100, file: !38, line: 259, type: !794)
!1106 = !DILocation(line: 259, column: 60, scope: !1100)
!1107 = !DILocation(line: 260, column: 28, scope: !1100)
!1108 = !DILocation(line: 260, column: 34, scope: !1100)
!1109 = !DILocation(line: 260, column: 39, scope: !1100)
!1110 = !DILocation(line: 260, column: 3, scope: !1100)
!1111 = !DILocation(line: 261, column: 1, scope: !1100)
!1112 = distinct !DISubprogram(name: "handleDivremOverflowImpl", linkageName: "_ZN7__ubsanL24handleDivremOverflowImplEP12OverflowDatamm", scope: !224, file: !38, line: 247, type: !988, scopeLine: 248, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1113 = !DILocalVariable(name: "Data", arg: 1, scope: !1112, file: !38, line: 247, type: !990)
!1114 = !DILocation(line: 247, column: 52, scope: !1112)
!1115 = !DILocalVariable(arg: 2, scope: !1112, file: !38, line: 247, type: !794)
!1116 = !DILocation(line: 247, column: 77, scope: !1112)
!1117 = !DILocalVariable(arg: 3, scope: !1112, file: !38, line: 248, type: !794)
!1118 = !DILocation(line: 248, column: 57, scope: !1112)
!1119 = !DILocation(line: 249, column: 7, scope: !1120)
!1120 = distinct !DILexicalBlock(scope: !1112, file: !38, line: 249, column: 7)
!1121 = !DILocation(line: 249, column: 13, scope: !1120)
!1122 = !DILocation(line: 249, column: 18, scope: !1120)
!1123 = !DILocation(line: 249, column: 7, scope: !1112)
!1124 = !DILocation(line: 250, column: 5, scope: !1120)
!1125 = !DILocalVariable(name: "ET", scope: !1126, file: !38, line: 252, type: !256)
!1126 = distinct !DILexicalBlock(scope: !1120, file: !38, line: 251, column: 8)
!1127 = !DILocation(line: 252, column: 15, scope: !1126)
!1128 = !DILocation(line: 253, column: 23, scope: !1126)
!1129 = !DILocation(line: 253, column: 5, scope: !1126)
!1130 = distinct !DISubprogram(name: "__ubsan_handle_divrem_overflow_abort", scope: !38, file: !38, line: 263, type: !988, scopeLine: 265, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1131 = !DILocalVariable(name: "Data", arg: 1, scope: !1130, file: !38, line: 263, type: !990)
!1132 = !DILocation(line: 263, column: 68, scope: !1130)
!1133 = !DILocalVariable(name: "LHS", arg: 2, scope: !1130, file: !38, line: 264, type: !794)
!1134 = !DILocation(line: 264, column: 66, scope: !1130)
!1135 = !DILocalVariable(name: "RHS", arg: 3, scope: !1130, file: !38, line: 265, type: !794)
!1136 = !DILocation(line: 265, column: 66, scope: !1130)
!1137 = !DILocation(line: 266, column: 28, scope: !1130)
!1138 = !DILocation(line: 266, column: 34, scope: !1130)
!1139 = !DILocation(line: 266, column: 39, scope: !1130)
!1140 = !DILocation(line: 266, column: 3, scope: !1130)
!1141 = !DILocation(line: 267, column: 1, scope: !1130)
!1142 = distinct !DISubprogram(name: "__ubsan_handle_shift_out_of_bounds", scope: !38, file: !38, line: 275, type: !1143, scopeLine: 277, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1143 = !DISubroutineType(types: !1144)
!1144 = !{null, !1145, !794, !794}
!1145 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1146, size: 64)
!1146 = !DICompositeType(tag: DW_TAG_structure_type, name: "ShiftOutOfBoundsData", file: !317, line: 43, size: 256, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS20ShiftOutOfBoundsData")
!1147 = !DILocalVariable(name: "Data", arg: 1, scope: !1142, file: !38, line: 275, type: !1145)
!1148 = !DILocation(line: 275, column: 74, scope: !1142)
!1149 = !DILocalVariable(name: "LHS", arg: 2, scope: !1142, file: !38, line: 276, type: !794)
!1150 = !DILocation(line: 276, column: 64, scope: !1142)
!1151 = !DILocalVariable(name: "RHS", arg: 3, scope: !1142, file: !38, line: 277, type: !794)
!1152 = !DILocation(line: 277, column: 64, scope: !1142)
!1153 = !DILocation(line: 278, column: 30, scope: !1142)
!1154 = !DILocation(line: 278, column: 36, scope: !1142)
!1155 = !DILocation(line: 278, column: 41, scope: !1142)
!1156 = !DILocation(line: 278, column: 3, scope: !1142)
!1157 = !DILocation(line: 279, column: 1, scope: !1142)
!1158 = distinct !DISubprogram(name: "handleShiftOutOfBoundsImpl", linkageName: "_ZN7__ubsanL26handleShiftOutOfBoundsImplEP20ShiftOutOfBoundsDatamm", scope: !224, file: !38, line: 269, type: !1143, scopeLine: 271, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1159 = !DILocalVariable(arg: 1, scope: !1158, file: !38, line: 269, type: !1145)
!1160 = !DILocation(line: 269, column: 71, scope: !1158)
!1161 = !DILocalVariable(arg: 2, scope: !1158, file: !38, line: 270, type: !794)
!1162 = !DILocation(line: 270, column: 59, scope: !1158)
!1163 = !DILocalVariable(arg: 3, scope: !1158, file: !38, line: 271, type: !794)
!1164 = !DILocation(line: 271, column: 59, scope: !1158)
!1165 = !DILocation(line: 272, column: 3, scope: !1158)
!1166 = distinct !DISubprogram(name: "__ubsan_handle_shift_out_of_bounds_abort", scope: !38, file: !38, line: 282, type: !1143, scopeLine: 283, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1167 = !DILocalVariable(name: "Data", arg: 1, scope: !1166, file: !38, line: 282, type: !1145)
!1168 = !DILocation(line: 282, column: 64, scope: !1166)
!1169 = !DILocalVariable(name: "LHS", arg: 2, scope: !1166, file: !38, line: 283, type: !794)
!1170 = !DILocation(line: 283, column: 54, scope: !1166)
!1171 = !DILocalVariable(name: "RHS", arg: 3, scope: !1166, file: !38, line: 283, type: !794)
!1172 = !DILocation(line: 283, column: 71, scope: !1166)
!1173 = !DILocation(line: 284, column: 30, scope: !1166)
!1174 = !DILocation(line: 284, column: 36, scope: !1166)
!1175 = !DILocation(line: 284, column: 41, scope: !1166)
!1176 = !DILocation(line: 284, column: 3, scope: !1166)
!1177 = !DILocation(line: 285, column: 1, scope: !1166)
!1178 = distinct !DISubprogram(name: "__ubsan_handle_out_of_bounds", scope: !38, file: !38, line: 293, type: !1179, scopeLine: 294, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1179 = !DISubroutineType(types: !1180)
!1180 = !{null, !1181, !794}
!1181 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1182, size: 64)
!1182 = !DICompositeType(tag: DW_TAG_structure_type, name: "OutOfBoundsData", file: !317, line: 49, size: 256, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS15OutOfBoundsData")
!1183 = !DILocalVariable(name: "Data", arg: 1, scope: !1178, file: !38, line: 293, type: !1181)
!1184 = !DILocation(line: 293, column: 63, scope: !1178)
!1185 = !DILocalVariable(name: "Index", arg: 2, scope: !1178, file: !38, line: 294, type: !794)
!1186 = !DILocation(line: 294, column: 58, scope: !1178)
!1187 = !DILocation(line: 295, column: 25, scope: !1178)
!1188 = !DILocation(line: 295, column: 31, scope: !1178)
!1189 = !DILocation(line: 295, column: 3, scope: !1178)
!1190 = !DILocation(line: 296, column: 1, scope: !1178)
!1191 = distinct !DISubprogram(name: "handleOutOfBoundsImpl", linkageName: "_ZN7__ubsanL21handleOutOfBoundsImplEP15OutOfBoundsDatam", scope: !224, file: !38, line: 287, type: !1179, scopeLine: 288, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1192 = !DILocalVariable(arg: 1, scope: !1191, file: !38, line: 287, type: !1181)
!1193 = !DILocation(line: 287, column: 61, scope: !1191)
!1194 = !DILocalVariable(arg: 2, scope: !1191, file: !38, line: 288, type: !794)
!1195 = !DILocation(line: 288, column: 56, scope: !1191)
!1196 = !DILocalVariable(name: "ET", scope: !1191, file: !38, line: 289, type: !256)
!1197 = !DILocation(line: 289, column: 13, scope: !1191)
!1198 = !DILocation(line: 290, column: 21, scope: !1191)
!1199 = !DILocation(line: 290, column: 3, scope: !1191)
!1200 = distinct !DISubprogram(name: "__ubsan_handle_out_of_bounds_abort", scope: !38, file: !38, line: 298, type: !1179, scopeLine: 299, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1201 = !DILocalVariable(name: "Data", arg: 1, scope: !1200, file: !38, line: 298, type: !1181)
!1202 = !DILocation(line: 298, column: 69, scope: !1200)
!1203 = !DILocalVariable(name: "Index", arg: 2, scope: !1200, file: !38, line: 299, type: !794)
!1204 = !DILocation(line: 299, column: 64, scope: !1200)
!1205 = !DILocation(line: 300, column: 25, scope: !1200)
!1206 = !DILocation(line: 300, column: 31, scope: !1200)
!1207 = !DILocation(line: 300, column: 3, scope: !1200)
!1208 = !DILocation(line: 301, column: 1, scope: !1200)
!1209 = distinct !DISubprogram(name: "__ubsan_handle_builtin_unreachable", scope: !38, file: !38, line: 308, type: !1210, scopeLine: 308, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1210 = !DISubroutineType(types: !1211)
!1211 = !{null, !1212}
!1212 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1213, size: 64)
!1213 = !DICompositeType(tag: DW_TAG_structure_type, name: "UnreachableData", file: !317, line: 55, size: 128, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS15UnreachableData")
!1214 = !DILocalVariable(name: "Data", arg: 1, scope: !1209, file: !38, line: 308, type: !1212)
!1215 = !DILocation(line: 308, column: 69, scope: !1209)
!1216 = !DILocation(line: 309, column: 32, scope: !1209)
!1217 = !DILocation(line: 309, column: 3, scope: !1209)
!1218 = !DILocation(line: 310, column: 1, scope: !1209)
!1219 = distinct !DISubprogram(name: "handleBuiltinUnreachableImpl", linkageName: "_ZN7__ubsanL28handleBuiltinUnreachableImplEP15UnreachableData", scope: !224, file: !38, line: 303, type: !1210, scopeLine: 303, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1220 = !DILocalVariable(arg: 1, scope: !1219, file: !38, line: 303, type: !1212)
!1221 = !DILocation(line: 303, column: 68, scope: !1219)
!1222 = !DILocalVariable(name: "ET", scope: !1219, file: !38, line: 304, type: !256)
!1223 = !DILocation(line: 304, column: 13, scope: !1219)
!1224 = !DILocation(line: 305, column: 21, scope: !1219)
!1225 = !DILocation(line: 305, column: 3, scope: !1219)
!1226 = distinct !DISubprogram(name: "__ubsan_handle_missing_return", scope: !38, file: !38, line: 317, type: !1210, scopeLine: 317, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1227 = !DILocalVariable(name: "Data", arg: 1, scope: !1226, file: !38, line: 317, type: !1212)
!1228 = !DILocation(line: 317, column: 64, scope: !1226)
!1229 = !DILocation(line: 318, column: 27, scope: !1226)
!1230 = !DILocation(line: 318, column: 3, scope: !1226)
!1231 = !DILocation(line: 319, column: 1, scope: !1226)
!1232 = distinct !DISubprogram(name: "handleMissingReturnImpl", linkageName: "_ZN7__ubsanL23handleMissingReturnImplEP15UnreachableData", scope: !224, file: !38, line: 312, type: !1210, scopeLine: 312, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1233 = !DILocalVariable(arg: 1, scope: !1232, file: !38, line: 312, type: !1212)
!1234 = !DILocation(line: 312, column: 63, scope: !1232)
!1235 = !DILocalVariable(name: "ET", scope: !1232, file: !38, line: 313, type: !256)
!1236 = !DILocation(line: 313, column: 13, scope: !1232)
!1237 = !DILocation(line: 314, column: 21, scope: !1232)
!1238 = !DILocation(line: 314, column: 3, scope: !1232)
!1239 = distinct !DISubprogram(name: "__ubsan_handle_vla_bound_not_positive", scope: !38, file: !38, line: 327, type: !1240, scopeLine: 328, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1240 = !DISubroutineType(types: !1241)
!1241 = !{null, !1242, !794}
!1242 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1243, size: 64)
!1243 = !DICompositeType(tag: DW_TAG_structure_type, name: "VLABoundData", file: !317, line: 59, size: 192, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS12VLABoundData")
!1244 = !DILocalVariable(name: "Data", arg: 1, scope: !1239, file: !38, line: 327, type: !1242)
!1245 = !DILocation(line: 327, column: 69, scope: !1239)
!1246 = !DILocalVariable(name: "Bound", arg: 2, scope: !1239, file: !38, line: 328, type: !794)
!1247 = !DILocation(line: 328, column: 67, scope: !1239)
!1248 = !DILocation(line: 329, column: 29, scope: !1239)
!1249 = !DILocation(line: 329, column: 35, scope: !1239)
!1250 = !DILocation(line: 329, column: 3, scope: !1239)
!1251 = !DILocation(line: 330, column: 1, scope: !1239)
!1252 = distinct !DISubprogram(name: "handleVLABoundNotPositive", linkageName: "_ZN7__ubsanL25handleVLABoundNotPositiveEP12VLABoundDatam", scope: !224, file: !38, line: 321, type: !1240, scopeLine: 322, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1253 = !DILocalVariable(arg: 1, scope: !1252, file: !38, line: 321, type: !1242)
!1254 = !DILocation(line: 321, column: 62, scope: !1252)
!1255 = !DILocalVariable(arg: 2, scope: !1252, file: !38, line: 322, type: !794)
!1256 = !DILocation(line: 322, column: 60, scope: !1252)
!1257 = !DILocalVariable(name: "ET", scope: !1252, file: !38, line: 323, type: !256)
!1258 = !DILocation(line: 323, column: 13, scope: !1252)
!1259 = !DILocation(line: 324, column: 21, scope: !1252)
!1260 = !DILocation(line: 324, column: 3, scope: !1252)
!1261 = distinct !DISubprogram(name: "__ubsan_handle_vla_bound_not_positive_abort", scope: !38, file: !38, line: 332, type: !1240, scopeLine: 333, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1262 = !DILocalVariable(name: "Data", arg: 1, scope: !1261, file: !38, line: 332, type: !1242)
!1263 = !DILocation(line: 332, column: 75, scope: !1261)
!1264 = !DILocalVariable(name: "Bound", arg: 2, scope: !1261, file: !38, line: 333, type: !794)
!1265 = !DILocation(line: 333, column: 73, scope: !1261)
!1266 = !DILocation(line: 334, column: 29, scope: !1261)
!1267 = !DILocation(line: 334, column: 35, scope: !1261)
!1268 = !DILocation(line: 334, column: 3, scope: !1261)
!1269 = !DILocation(line: 335, column: 1, scope: !1261)
!1270 = distinct !DISubprogram(name: "__ubsan_handle_float_cast_overflow", scope: !38, file: !38, line: 342, type: !1271, scopeLine: 343, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1271 = !DISubroutineType(types: !1272)
!1272 = !{null, !1273, !794}
!1273 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)
!1274 = !DILocalVariable(name: "Data", arg: 1, scope: !1270, file: !38, line: 342, type: !1273)
!1275 = !DILocation(line: 342, column: 58, scope: !1270)
!1276 = !DILocalVariable(name: "From", arg: 2, scope: !1270, file: !38, line: 343, type: !794)
!1277 = !DILocation(line: 343, column: 64, scope: !1270)
!1278 = !DILocation(line: 344, column: 27, scope: !1270)
!1279 = !DILocation(line: 344, column: 33, scope: !1270)
!1280 = !DILocation(line: 344, column: 3, scope: !1270)
!1281 = !DILocation(line: 345, column: 1, scope: !1270)
!1282 = distinct !DISubprogram(name: "handleFloatCastOverflow", linkageName: "_ZN7__ubsanL23handleFloatCastOverflowEPvm", scope: !224, file: !38, line: 337, type: !1271, scopeLine: 337, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1283 = !DILocalVariable(arg: 1, scope: !1282, file: !38, line: 337, type: !1273)
!1284 = !DILocation(line: 337, column: 55, scope: !1282)
!1285 = !DILocalVariable(arg: 2, scope: !1282, file: !38, line: 337, type: !794)
!1286 = !DILocation(line: 337, column: 77, scope: !1282)
!1287 = !DILocalVariable(name: "ET", scope: !1282, file: !38, line: 338, type: !256)
!1288 = !DILocation(line: 338, column: 13, scope: !1282)
!1289 = !DILocation(line: 339, column: 21, scope: !1282)
!1290 = !DILocation(line: 339, column: 3, scope: !1282)
!1291 = distinct !DISubprogram(name: "__ubsan_handle_float_cast_overflow_abort", scope: !38, file: !38, line: 347, type: !1271, scopeLine: 348, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1292 = !DILocalVariable(name: "Data", arg: 1, scope: !1291, file: !38, line: 347, type: !1273)
!1293 = !DILocation(line: 347, column: 64, scope: !1291)
!1294 = !DILocalVariable(name: "From", arg: 2, scope: !1291, file: !38, line: 348, type: !794)
!1295 = !DILocation(line: 348, column: 70, scope: !1291)
!1296 = !DILocation(line: 349, column: 27, scope: !1291)
!1297 = !DILocation(line: 349, column: 33, scope: !1291)
!1298 = !DILocation(line: 349, column: 3, scope: !1291)
!1299 = !DILocation(line: 350, column: 1, scope: !1291)
!1300 = distinct !DISubprogram(name: "__ubsan_handle_load_invalid_value", scope: !38, file: !38, line: 357, type: !1301, scopeLine: 358, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1301 = !DISubroutineType(types: !1302)
!1302 = !{null, !1303, !794}
!1303 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1304, size: 64)
!1304 = !DICompositeType(tag: DW_TAG_structure_type, name: "InvalidValueData", file: !317, line: 64, size: 192, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS16InvalidValueData")
!1305 = !DILocalVariable(name: "Data", arg: 1, scope: !1300, file: !38, line: 357, type: !1303)
!1306 = !DILocation(line: 357, column: 69, scope: !1300)
!1307 = !DILocalVariable(name: "Val", arg: 2, scope: !1300, file: !38, line: 358, type: !794)
!1308 = !DILocation(line: 358, column: 63, scope: !1300)
!1309 = !DILocation(line: 359, column: 26, scope: !1300)
!1310 = !DILocation(line: 359, column: 32, scope: !1300)
!1311 = !DILocation(line: 359, column: 3, scope: !1300)
!1312 = !DILocation(line: 360, column: 1, scope: !1300)
!1313 = distinct !DISubprogram(name: "handleLoadInvalidValue", linkageName: "_ZN7__ubsanL22handleLoadInvalidValueEP16InvalidValueDatam", scope: !224, file: !38, line: 352, type: !1301, scopeLine: 353, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1314 = !DILocalVariable(arg: 1, scope: !1313, file: !38, line: 352, type: !1303)
!1315 = !DILocation(line: 352, column: 63, scope: !1313)
!1316 = !DILocalVariable(arg: 2, scope: !1313, file: !38, line: 353, type: !794)
!1317 = !DILocation(line: 353, column: 55, scope: !1313)
!1318 = !DILocation(line: 354, column: 3, scope: !1313)
!1319 = distinct !DISubprogram(name: "__ubsan_handle_load_invalid_value_abort", scope: !38, file: !38, line: 361, type: !1301, scopeLine: 362, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1320 = !DILocalVariable(name: "Data", arg: 1, scope: !1319, file: !38, line: 361, type: !1303)
!1321 = !DILocation(line: 361, column: 75, scope: !1319)
!1322 = !DILocalVariable(name: "Val", arg: 2, scope: !1319, file: !38, line: 362, type: !794)
!1323 = !DILocation(line: 362, column: 69, scope: !1319)
!1324 = !DILocation(line: 363, column: 26, scope: !1319)
!1325 = !DILocation(line: 363, column: 32, scope: !1319)
!1326 = !DILocation(line: 363, column: 3, scope: !1319)
!1327 = !DILocation(line: 364, column: 1, scope: !1319)
!1328 = distinct !DISubprogram(name: "__ubsan_handle_implicit_conversion", scope: !38, file: !38, line: 404, type: !1329, scopeLine: 406, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1329 = !DISubroutineType(types: !1330)
!1330 = !{null, !1331, !794, !794}
!1331 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1332, size: 64)
!1332 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ImplicitConversionData", file: !317, line: 79, size: 320, flags: DIFlagTypePassByValue | DIFlagNonTrivial, elements: !1333, identifier: "_ZTS22ImplicitConversionData")
!1333 = !{!1334, !1335, !1336, !1337}
!1334 = !DIDerivedType(tag: DW_TAG_member, name: "Loc", scope: !1332, file: !317, line: 80, baseType: !789, size: 128)
!1335 = !DIDerivedType(tag: DW_TAG_member, name: "FromType", scope: !1332, file: !317, line: 81, baseType: !791, size: 64, offset: 128)
!1336 = !DIDerivedType(tag: DW_TAG_member, name: "ToType", scope: !1332, file: !317, line: 82, baseType: !791, size: 64, offset: 192)
!1337 = !DIDerivedType(tag: DW_TAG_member, name: "Kind", scope: !1332, file: !317, line: 83, baseType: !777, size: 8, offset: 256)
!1338 = !DILocalVariable(name: "Data", arg: 1, scope: !1328, file: !38, line: 404, type: !1331)
!1339 = !DILocation(line: 404, column: 76, scope: !1328)
!1340 = !DILocalVariable(name: "Src", arg: 2, scope: !1328, file: !38, line: 405, type: !794)
!1341 = !DILocation(line: 405, column: 64, scope: !1328)
!1342 = !DILocalVariable(name: "Dst", arg: 3, scope: !1328, file: !38, line: 406, type: !794)
!1343 = !DILocation(line: 406, column: 64, scope: !1328)
!1344 = !DILocation(line: 407, column: 28, scope: !1328)
!1345 = !DILocation(line: 407, column: 34, scope: !1328)
!1346 = !DILocation(line: 407, column: 39, scope: !1328)
!1347 = !DILocation(line: 407, column: 3, scope: !1328)
!1348 = !DILocation(line: 408, column: 1, scope: !1328)
!1349 = distinct !DISubprogram(name: "handleImplicitConversion", linkageName: "_ZN7__ubsanL24handleImplicitConversionEP22ImplicitConversionDatamm", scope: !224, file: !38, line: 366, type: !1329, scopeLine: 367, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1350 = !DILocalVariable(name: "Data", arg: 1, scope: !1349, file: !38, line: 366, type: !1331)
!1351 = !DILocation(line: 366, column: 62, scope: !1349)
!1352 = !DILocalVariable(arg: 2, scope: !1349, file: !38, line: 367, type: !794)
!1353 = !DILocation(line: 367, column: 57, scope: !1349)
!1354 = !DILocalVariable(arg: 3, scope: !1349, file: !38, line: 367, type: !794)
!1355 = !DILocation(line: 367, column: 78, scope: !1349)
!1356 = !DILocalVariable(name: "ET", scope: !1349, file: !38, line: 368, type: !256)
!1357 = !DILocation(line: 368, column: 13, scope: !1349)
!1358 = !DILocalVariable(name: "SrcTy", scope: !1349, file: !38, line: 370, type: !791)
!1359 = !DILocation(line: 370, column: 25, scope: !1349)
!1360 = !DILocation(line: 370, column: 33, scope: !1349)
!1361 = !DILocation(line: 370, column: 39, scope: !1349)
!1362 = !DILocalVariable(name: "DstTy", scope: !1349, file: !38, line: 371, type: !791)
!1363 = !DILocation(line: 371, column: 25, scope: !1349)
!1364 = !DILocation(line: 371, column: 33, scope: !1349)
!1365 = !DILocation(line: 371, column: 39, scope: !1349)
!1366 = !DILocalVariable(name: "SrcSigned", scope: !1349, file: !38, line: 373, type: !248)
!1367 = !DILocation(line: 373, column: 8, scope: !1349)
!1368 = !DILocation(line: 373, column: 20, scope: !1349)
!1369 = !DILocation(line: 373, column: 26, scope: !1349)
!1370 = !DILocalVariable(name: "DstSigned", scope: !1349, file: !38, line: 374, type: !248)
!1371 = !DILocation(line: 374, column: 8, scope: !1349)
!1372 = !DILocation(line: 374, column: 20, scope: !1349)
!1373 = !DILocation(line: 374, column: 26, scope: !1349)
!1374 = !DILocation(line: 376, column: 11, scope: !1349)
!1375 = !DILocation(line: 376, column: 17, scope: !1349)
!1376 = !DILocation(line: 376, column: 3, scope: !1349)
!1377 = !DILocation(line: 381, column: 10, scope: !1378)
!1378 = distinct !DILexicalBlock(scope: !1379, file: !38, line: 381, column: 9)
!1379 = distinct !DILexicalBlock(scope: !1380, file: !38, line: 377, column: 32)
!1380 = distinct !DILexicalBlock(scope: !1349, file: !38, line: 376, column: 23)
!1381 = !DILocation(line: 381, column: 20, scope: !1378)
!1382 = !DILocation(line: 381, column: 24, scope: !1378)
!1383 = !DILocation(line: 381, column: 9, scope: !1379)
!1384 = !DILocation(line: 382, column: 10, scope: !1385)
!1385 = distinct !DILexicalBlock(scope: !1378, file: !38, line: 381, column: 35)
!1386 = !DILocation(line: 383, column: 5, scope: !1385)
!1387 = !DILocation(line: 384, column: 10, scope: !1388)
!1388 = distinct !DILexicalBlock(scope: !1378, file: !38, line: 383, column: 12)
!1389 = !DILocation(line: 389, column: 8, scope: !1380)
!1390 = !DILocation(line: 390, column: 5, scope: !1380)
!1391 = !DILocation(line: 392, column: 8, scope: !1380)
!1392 = !DILocation(line: 393, column: 5, scope: !1380)
!1393 = !DILocation(line: 395, column: 8, scope: !1380)
!1394 = !DILocation(line: 396, column: 5, scope: !1380)
!1395 = !DILocation(line: 398, column: 8, scope: !1380)
!1396 = !DILocation(line: 399, column: 5, scope: !1380)
!1397 = !DILocation(line: 401, column: 21, scope: !1349)
!1398 = !DILocation(line: 401, column: 3, scope: !1349)
!1399 = distinct !DISubprogram(name: "__ubsan_handle_implicit_conversion_abort", scope: !38, file: !38, line: 411, type: !1329, scopeLine: 412, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1400 = !DILocalVariable(name: "Data", arg: 1, scope: !1399, file: !38, line: 411, type: !1331)
!1401 = !DILocation(line: 411, column: 66, scope: !1399)
!1402 = !DILocalVariable(name: "Src", arg: 2, scope: !1399, file: !38, line: 412, type: !794)
!1403 = !DILocation(line: 412, column: 54, scope: !1399)
!1404 = !DILocalVariable(name: "Dst", arg: 3, scope: !1399, file: !38, line: 412, type: !794)
!1405 = !DILocation(line: 412, column: 71, scope: !1399)
!1406 = !DILocation(line: 413, column: 28, scope: !1399)
!1407 = !DILocation(line: 413, column: 34, scope: !1399)
!1408 = !DILocation(line: 413, column: 39, scope: !1399)
!1409 = !DILocation(line: 413, column: 3, scope: !1399)
!1410 = !DILocation(line: 414, column: 1, scope: !1399)
!1411 = distinct !DISubprogram(name: "__ubsan_handle_invalid_builtin", scope: !38, file: !38, line: 421, type: !1412, scopeLine: 421, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1412 = !DISubroutineType(types: !1413)
!1413 = !{null, !1414}
!1414 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1415, size: 64)
!1415 = !DICompositeType(tag: DW_TAG_structure_type, name: "InvalidBuiltinData", file: !317, line: 86, size: 192, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS18InvalidBuiltinData")
!1416 = !DILocalVariable(name: "Data", arg: 1, scope: !1411, file: !38, line: 421, type: !1414)
!1417 = !DILocation(line: 421, column: 68, scope: !1411)
!1418 = !DILocation(line: 422, column: 24, scope: !1411)
!1419 = !DILocation(line: 422, column: 3, scope: !1411)
!1420 = !DILocation(line: 423, column: 1, scope: !1411)
!1421 = distinct !DISubprogram(name: "handleInvalidBuiltin", linkageName: "_ZN7__ubsanL20handleInvalidBuiltinEP18InvalidBuiltinData", scope: !224, file: !38, line: 416, type: !1412, scopeLine: 416, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1422 = !DILocalVariable(arg: 1, scope: !1421, file: !38, line: 416, type: !1414)
!1423 = !DILocation(line: 416, column: 63, scope: !1421)
!1424 = !DILocalVariable(name: "ET", scope: !1421, file: !38, line: 417, type: !256)
!1425 = !DILocation(line: 417, column: 13, scope: !1421)
!1426 = !DILocation(line: 418, column: 21, scope: !1421)
!1427 = !DILocation(line: 418, column: 3, scope: !1421)
!1428 = distinct !DISubprogram(name: "__ubsan_handle_invalid_builtin_abort", scope: !38, file: !38, line: 425, type: !1412, scopeLine: 425, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1429 = !DILocalVariable(name: "Data", arg: 1, scope: !1428, file: !38, line: 425, type: !1414)
!1430 = !DILocation(line: 425, column: 74, scope: !1428)
!1431 = !DILocation(line: 426, column: 24, scope: !1428)
!1432 = !DILocation(line: 426, column: 3, scope: !1428)
!1433 = !DILocation(line: 427, column: 1, scope: !1428)
!1434 = distinct !DISubprogram(name: "__ubsan_handle_nonnull_return_v1", scope: !38, file: !38, line: 436, type: !1435, scopeLine: 437, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1435 = !DISubroutineType(types: !1436)
!1436 = !{null, !1437, !1439}
!1437 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1438, size: 64)
!1438 = !DICompositeType(tag: DW_TAG_structure_type, name: "NonNullReturnData", file: !317, line: 91, size: 128, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS17NonNullReturnData")
!1439 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !789, size: 64)
!1440 = !DILocalVariable(name: "Data", arg: 1, scope: !1434, file: !38, line: 436, type: !1437)
!1441 = !DILocation(line: 436, column: 69, scope: !1434)
!1442 = !DILocalVariable(name: "LocPtr", arg: 2, scope: !1434, file: !38, line: 437, type: !1439)
!1443 = !DILocation(line: 437, column: 66, scope: !1434)
!1444 = !DILocation(line: 438, column: 23, scope: !1434)
!1445 = !DILocation(line: 438, column: 29, scope: !1434)
!1446 = !DILocation(line: 438, column: 3, scope: !1434)
!1447 = !DILocation(line: 439, column: 1, scope: !1434)
!1448 = distinct !DISubprogram(name: "handleNonNullReturn", linkageName: "_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb", scope: !224, file: !38, line: 429, type: !1449, scopeLine: 430, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1449 = !DISubroutineType(types: !1450)
!1450 = !{null, !1437, !1439, !248}
!1451 = !DILocalVariable(arg: 1, scope: !1448, file: !38, line: 429, type: !1437)
!1452 = !DILocation(line: 429, column: 61, scope: !1448)
!1453 = !DILocalVariable(arg: 2, scope: !1448, file: !38, line: 430, type: !1439)
!1454 = !DILocation(line: 430, column: 60, scope: !1448)
!1455 = !DILocalVariable(name: "IsAttr", arg: 3, scope: !1448, file: !38, line: 430, type: !248)
!1456 = !DILocation(line: 430, column: 67, scope: !1448)
!1457 = !DILocalVariable(name: "ET", scope: !1448, file: !38, line: 431, type: !256)
!1458 = !DILocation(line: 431, column: 13, scope: !1448)
!1459 = !DILocation(line: 431, column: 18, scope: !1448)
!1460 = !DILocation(line: 433, column: 21, scope: !1448)
!1461 = !DILocation(line: 433, column: 3, scope: !1448)
!1462 = distinct !DISubprogram(name: "__ubsan_handle_nonnull_return_v1_abort", scope: !38, file: !38, line: 441, type: !1435, scopeLine: 442, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1463 = !DILocalVariable(name: "Data", arg: 1, scope: !1462, file: !38, line: 441, type: !1437)
!1464 = !DILocation(line: 441, column: 75, scope: !1462)
!1465 = !DILocalVariable(name: "LocPtr", arg: 2, scope: !1462, file: !38, line: 442, type: !1439)
!1466 = !DILocation(line: 442, column: 72, scope: !1462)
!1467 = !DILocation(line: 443, column: 23, scope: !1462)
!1468 = !DILocation(line: 443, column: 29, scope: !1462)
!1469 = !DILocation(line: 443, column: 3, scope: !1462)
!1470 = !DILocation(line: 444, column: 1, scope: !1462)
!1471 = distinct !DISubprogram(name: "__ubsan_handle_nullability_return_v1", scope: !38, file: !38, line: 446, type: !1435, scopeLine: 447, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1472 = !DILocalVariable(name: "Data", arg: 1, scope: !1471, file: !38, line: 446, type: !1437)
!1473 = !DILocation(line: 446, column: 73, scope: !1471)
!1474 = !DILocalVariable(name: "LocPtr", arg: 2, scope: !1471, file: !38, line: 447, type: !1439)
!1475 = !DILocation(line: 447, column: 70, scope: !1471)
!1476 = !DILocation(line: 448, column: 23, scope: !1471)
!1477 = !DILocation(line: 448, column: 29, scope: !1471)
!1478 = !DILocation(line: 448, column: 3, scope: !1471)
!1479 = !DILocation(line: 449, column: 1, scope: !1471)
!1480 = distinct !DISubprogram(name: "__ubsan_handle_nullability_return_v1_abort", scope: !38, file: !38, line: 452, type: !1435, scopeLine: 453, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1481 = !DILocalVariable(name: "Data", arg: 1, scope: !1480, file: !38, line: 452, type: !1437)
!1482 = !DILocation(line: 452, column: 63, scope: !1480)
!1483 = !DILocalVariable(name: "LocPtr", arg: 2, scope: !1480, file: !38, line: 453, type: !1439)
!1484 = !DILocation(line: 453, column: 60, scope: !1480)
!1485 = !DILocation(line: 454, column: 23, scope: !1480)
!1486 = !DILocation(line: 454, column: 29, scope: !1480)
!1487 = !DILocation(line: 454, column: 3, scope: !1480)
!1488 = !DILocation(line: 455, column: 1, scope: !1480)
!1489 = distinct !DISubprogram(name: "__ubsan_handle_nonnull_arg", scope: !38, file: !38, line: 463, type: !1490, scopeLine: 463, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1490 = !DISubroutineType(types: !1491)
!1491 = !{null, !1492}
!1492 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1493, size: 64)
!1493 = !DICompositeType(tag: DW_TAG_structure_type, name: "NonNullArgData", file: !317, line: 95, size: 320, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS14NonNullArgData")
!1494 = !DILocalVariable(name: "Data", arg: 1, scope: !1489, file: !38, line: 463, type: !1492)
!1495 = !DILocation(line: 463, column: 60, scope: !1489)
!1496 = !DILocation(line: 464, column: 20, scope: !1489)
!1497 = !DILocation(line: 464, column: 3, scope: !1489)
!1498 = !DILocation(line: 465, column: 1, scope: !1489)
!1499 = distinct !DISubprogram(name: "handleNonNullArg", linkageName: "_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab", scope: !224, file: !38, line: 457, type: !1500, scopeLine: 457, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1500 = !DISubroutineType(types: !1501)
!1501 = !{null, !1492, !248}
!1502 = !DILocalVariable(arg: 1, scope: !1499, file: !38, line: 457, type: !1492)
!1503 = !DILocation(line: 457, column: 55, scope: !1499)
!1504 = !DILocalVariable(name: "IsAttr", arg: 2, scope: !1499, file: !38, line: 457, type: !248)
!1505 = !DILocation(line: 457, column: 62, scope: !1499)
!1506 = !DILocalVariable(name: "ET", scope: !1499, file: !38, line: 458, type: !256)
!1507 = !DILocation(line: 458, column: 13, scope: !1499)
!1508 = !DILocation(line: 458, column: 18, scope: !1499)
!1509 = !DILocation(line: 460, column: 21, scope: !1499)
!1510 = !DILocation(line: 460, column: 3, scope: !1499)
!1511 = distinct !DISubprogram(name: "__ubsan_handle_nonnull_arg_abort", scope: !38, file: !38, line: 467, type: !1490, scopeLine: 467, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1512 = !DILocalVariable(name: "Data", arg: 1, scope: !1511, file: !38, line: 467, type: !1492)
!1513 = !DILocation(line: 467, column: 66, scope: !1511)
!1514 = !DILocation(line: 468, column: 20, scope: !1511)
!1515 = !DILocation(line: 468, column: 3, scope: !1511)
!1516 = !DILocation(line: 469, column: 1, scope: !1511)
!1517 = distinct !DISubprogram(name: "__ubsan_handle_nullability_arg", scope: !38, file: !38, line: 471, type: !1490, scopeLine: 471, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1518 = !DILocalVariable(name: "Data", arg: 1, scope: !1517, file: !38, line: 471, type: !1492)
!1519 = !DILocation(line: 471, column: 64, scope: !1517)
!1520 = !DILocation(line: 472, column: 20, scope: !1517)
!1521 = !DILocation(line: 472, column: 3, scope: !1517)
!1522 = !DILocation(line: 473, column: 1, scope: !1517)
!1523 = distinct !DISubprogram(name: "__ubsan_handle_nullability_arg_abort", scope: !38, file: !38, line: 475, type: !1490, scopeLine: 475, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1524 = !DILocalVariable(name: "Data", arg: 1, scope: !1523, file: !38, line: 475, type: !1492)
!1525 = !DILocation(line: 475, column: 70, scope: !1523)
!1526 = !DILocation(line: 477, column: 20, scope: !1523)
!1527 = !DILocation(line: 477, column: 3, scope: !1523)
!1528 = !DILocation(line: 478, column: 1, scope: !1523)
!1529 = distinct !DISubprogram(name: "__ubsan_handle_pointer_overflow", scope: !38, file: !38, line: 494, type: !1530, scopeLine: 496, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1530 = !DISubroutineType(types: !1531)
!1531 = !{null, !1532, !794, !794}
!1532 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1533, size: 64)
!1533 = !DICompositeType(tag: DW_TAG_structure_type, name: "PointerOverflowData", file: !317, line: 101, size: 128, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS19PointerOverflowData")
!1534 = !DILocalVariable(name: "Data", arg: 1, scope: !1529, file: !38, line: 494, type: !1532)
!1535 = !DILocation(line: 494, column: 70, scope: !1529)
!1536 = !DILocalVariable(name: "Base", arg: 2, scope: !1529, file: !38, line: 495, type: !794)
!1537 = !DILocation(line: 495, column: 61, scope: !1529)
!1538 = !DILocalVariable(name: "Result", arg: 3, scope: !1529, file: !38, line: 496, type: !794)
!1539 = !DILocation(line: 496, column: 61, scope: !1529)
!1540 = !DILocation(line: 498, column: 29, scope: !1529)
!1541 = !DILocation(line: 498, column: 35, scope: !1529)
!1542 = !DILocation(line: 498, column: 41, scope: !1529)
!1543 = !DILocation(line: 498, column: 3, scope: !1529)
!1544 = !DILocation(line: 499, column: 1, scope: !1529)
!1545 = distinct !DISubprogram(name: "handlePointerOverflowImpl", linkageName: "_ZN7__ubsanL25handlePointerOverflowImplEP19PointerOverflowDatamm", scope: !224, file: !38, line: 480, type: !1530, scopeLine: 481, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1546 = !DILocalVariable(arg: 1, scope: !1545, file: !38, line: 480, type: !1532)
!1547 = !DILocation(line: 480, column: 69, scope: !1545)
!1548 = !DILocalVariable(name: "Base", arg: 2, scope: !1545, file: !38, line: 481, type: !794)
!1549 = !DILocation(line: 481, column: 51, scope: !1545)
!1550 = !DILocalVariable(name: "Result", arg: 3, scope: !1545, file: !38, line: 481, type: !794)
!1551 = !DILocation(line: 481, column: 69, scope: !1545)
!1552 = !DILocalVariable(name: "ET", scope: !1545, file: !38, line: 482, type: !256)
!1553 = !DILocation(line: 482, column: 13, scope: !1545)
!1554 = !DILocation(line: 483, column: 7, scope: !1555)
!1555 = distinct !DILexicalBlock(scope: !1545, file: !38, line: 483, column: 7)
!1556 = !DILocation(line: 483, column: 12, scope: !1555)
!1557 = !DILocation(line: 483, column: 17, scope: !1555)
!1558 = !DILocation(line: 484, column: 8, scope: !1555)
!1559 = !DILocation(line: 484, column: 5, scope: !1555)
!1560 = !DILocation(line: 485, column: 12, scope: !1561)
!1561 = distinct !DILexicalBlock(scope: !1555, file: !38, line: 485, column: 12)
!1562 = !DILocation(line: 485, column: 17, scope: !1561)
!1563 = !DILocation(line: 485, column: 22, scope: !1561)
!1564 = !DILocation(line: 486, column: 8, scope: !1561)
!1565 = !DILocation(line: 486, column: 5, scope: !1561)
!1566 = !DILocation(line: 487, column: 12, scope: !1567)
!1567 = distinct !DILexicalBlock(scope: !1561, file: !38, line: 487, column: 12)
!1568 = !DILocation(line: 487, column: 17, scope: !1567)
!1569 = !DILocation(line: 487, column: 22, scope: !1567)
!1570 = !DILocation(line: 488, column: 8, scope: !1567)
!1571 = !DILocation(line: 488, column: 5, scope: !1567)
!1572 = !DILocation(line: 490, column: 8, scope: !1567)
!1573 = !DILocation(line: 491, column: 21, scope: !1545)
!1574 = !DILocation(line: 491, column: 3, scope: !1545)
!1575 = distinct !DISubprogram(name: "__ubsan_handle_pointer_overflow_abort", scope: !38, file: !38, line: 501, type: !1530, scopeLine: 503, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1576 = !DILocalVariable(name: "Data", arg: 1, scope: !1575, file: !38, line: 501, type: !1532)
!1577 = !DILocation(line: 501, column: 76, scope: !1575)
!1578 = !DILocalVariable(name: "Base", arg: 2, scope: !1575, file: !38, line: 502, type: !794)
!1579 = !DILocation(line: 502, column: 67, scope: !1575)
!1580 = !DILocalVariable(name: "Result", arg: 3, scope: !1575, file: !38, line: 503, type: !794)
!1581 = !DILocation(line: 503, column: 67, scope: !1575)
!1582 = !DILocation(line: 505, column: 29, scope: !1575)
!1583 = !DILocation(line: 505, column: 35, scope: !1575)
!1584 = !DILocation(line: 505, column: 41, scope: !1575)
!1585 = !DILocation(line: 505, column: 3, scope: !1575)
!1586 = !DILocation(line: 506, column: 1, scope: !1575)
!1587 = distinct !DISubprogram(name: "__ubsan_handle_function_type_mismatch", scope: !38, file: !38, line: 516, type: !1588, scopeLine: 517, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1588 = !DISubroutineType(types: !1589)
!1589 = !{null, !1590, !794}
!1590 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1591, size: 64)
!1591 = !DICompositeType(tag: DW_TAG_structure_type, name: "FunctionTypeMismatchData", file: !317, line: 106, size: 192, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS24FunctionTypeMismatchData")
!1592 = !DILocalVariable(name: "Data", arg: 1, scope: !1587, file: !38, line: 516, type: !1590)
!1593 = !DILocation(line: 516, column: 65, scope: !1587)
!1594 = !DILocalVariable(name: "Function", arg: 2, scope: !1587, file: !38, line: 517, type: !794)
!1595 = !DILocation(line: 517, column: 51, scope: !1587)
!1596 = !DILocation(line: 518, column: 30, scope: !1587)
!1597 = !DILocation(line: 518, column: 36, scope: !1587)
!1598 = !DILocation(line: 518, column: 3, scope: !1587)
!1599 = !DILocation(line: 519, column: 1, scope: !1587)
!1600 = distinct !DISubprogram(name: "handleFunctionTypeMismatch", linkageName: "_ZN7__ubsanL26handleFunctionTypeMismatchEP24FunctionTypeMismatchDatam", scope: !224, file: !38, line: 509, type: !1588, scopeLine: 510, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1601 = !DILocalVariable(arg: 1, scope: !1600, file: !38, line: 509, type: !1590)
!1602 = !DILocation(line: 509, column: 75, scope: !1600)
!1603 = !DILocalVariable(arg: 2, scope: !1600, file: !38, line: 510, type: !794)
!1604 = !DILocation(line: 510, column: 64, scope: !1600)
!1605 = !DILocalVariable(name: "ET", scope: !1600, file: !38, line: 511, type: !256)
!1606 = !DILocation(line: 511, column: 13, scope: !1600)
!1607 = !DILocation(line: 512, column: 21, scope: !1600)
!1608 = !DILocation(line: 512, column: 3, scope: !1600)
!1609 = distinct !DISubprogram(name: "__ubsan_handle_function_type_mismatch_abort", scope: !38, file: !38, line: 522, type: !1588, scopeLine: 523, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1610 = !DILocalVariable(name: "Data", arg: 1, scope: !1609, file: !38, line: 522, type: !1590)
!1611 = !DILocation(line: 522, column: 71, scope: !1609)
!1612 = !DILocalVariable(name: "Function", arg: 2, scope: !1609, file: !38, line: 523, type: !794)
!1613 = !DILocation(line: 523, column: 57, scope: !1609)
!1614 = !DILocation(line: 524, column: 30, scope: !1609)
!1615 = !DILocation(line: 524, column: 36, scope: !1609)
!1616 = !DILocation(line: 524, column: 3, scope: !1609)
!1617 = !DILocation(line: 525, column: 1, scope: !1609)
!1618 = distinct !DISubprogram(name: "klee_overshift_check", scope: !201, file: !201, line: 20, type: !1619, scopeLine: 20, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !318, retainedNodes: !334)
!1619 = !DISubroutineType(types: !1620)
!1620 = !{null, !1621, !1621}
!1621 = !DIBasicType(name: "unsigned long long", size: 64, encoding: DW_ATE_unsigned)
!1622 = !DILocalVariable(name: "bitWidth", arg: 1, scope: !1618, file: !201, line: 20, type: !1621)
!1623 = !DILocation(line: 20, column: 46, scope: !1618)
!1624 = !DILocalVariable(name: "shift", arg: 2, scope: !1618, file: !201, line: 20, type: !1621)
!1625 = !DILocation(line: 20, column: 75, scope: !1618)
!1626 = !DILocation(line: 21, column: 7, scope: !1627)
!1627 = distinct !DILexicalBlock(scope: !1618, file: !201, line: 21, column: 7)
!1628 = !DILocation(line: 21, column: 16, scope: !1627)
!1629 = !DILocation(line: 21, column: 13, scope: !1627)
!1630 = !DILocation(line: 21, column: 7, scope: !1618)
!1631 = !DILocation(line: 27, column: 5, scope: !1632)
!1632 = distinct !DILexicalBlock(scope: !1627, file: !201, line: 21, column: 26)
!1633 = !DILocation(line: 29, column: 1, scope: !1618)
