; ModuleID = '/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo/spikes/clight-permute/build/equiv-alive2/rejected-large-extended/n64/linked.bc'
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
@0 = private unnamed_addr constant { i16, i16, [20 x i8] } { i16 -1, i16 0, [20 x i8] c"'unsigned int[131]'\00" }
@1 = private unnamed_addr constant { i16, i16, [15 x i8] } { i16 0, i16 10, [15 x i8] c"'unsigned int'\00" }
@2 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 25, i32 18 }, ptr @0, ptr @1 }
@3 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 27, i32 22 }, ptr @0, ptr @1 }
@4 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 27, i32 34 }, ptr @0, ptr @1 }
@5 = private unnamed_addr global { { ptr, i32, i32 }, ptr, ptr } { { ptr, i32, i32 } { ptr @.src, i32 28, i32 26 }, ptr @0, ptr @1 }
@6 = private unnamed_addr constant { i16, i16, [19 x i8] } { i16 -1, i16 0, [19 x i8] c"'unsigned int[64]'\00" }
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
  %1 = alloca [131 x i32], align 16
  %2 = alloca [64 x i32], align 16
  %3 = alloca [64 x i32], align 16
  %4 = alloca [64 x i32], align 16
  %5 = alloca [64 x i32], align 16
  %6 = alloca [128 x i32], align 16
  %7 = alloca [3 x i32], align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
    #dbg_declare(ptr %1, !640, !DIExpression(), !644)
    #dbg_declare(ptr %2, !645, !DIExpression(), !649)
    #dbg_declare(ptr %3, !650, !DIExpression(), !651)
    #dbg_declare(ptr %4, !652, !DIExpression(), !653)
    #dbg_declare(ptr %5, !654, !DIExpression(), !655)
    #dbg_declare(ptr %6, !656, !DIExpression(), !660)
    #dbg_declare(ptr %7, !661, !DIExpression(), !665)
  %15 = getelementptr inbounds [131 x i32], ptr %1, i64 0, i64 0, !dbg !666
  call void @klee_make_symbolic(ptr noundef %15, i64 noundef 524, ptr noundef @.str), !dbg !667
    #dbg_declare(ptr %8, !668, !DIExpression(), !669)
  store i32 1, ptr %8, align 4, !dbg !669
    #dbg_declare(ptr %9, !670, !DIExpression(), !672)
  store i32 0, ptr %9, align 4, !dbg !672
  br label %16, !dbg !673

16:                                               ; preds = %146, %0
  %17 = load i32, ptr %9, align 4, !dbg !674
  %18 = icmp ult i32 %17, 64, !dbg !676
  br i1 %18, label %19, label %149, !dbg !677

19:                                               ; preds = %16
  %20 = load i32, ptr %9, align 4, !dbg !678
  %21 = zext i32 %20 to i64, !dbg !680, !nosanitize !334
  %22 = icmp ult i64 %21, 131, !dbg !680, !nosanitize !334
  br i1 %22, label %25, label %23, !dbg !680, !prof !681, !nosanitize !334

23:                                               ; preds = %19
  %24 = zext i32 %20 to i64, !dbg !680, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @2, i64 %24) #7, !dbg !680, !nosanitize !334
  unreachable, !dbg !680, !nosanitize !334

25:                                               ; preds = %19
  %26 = zext i32 %20 to i64, !dbg !680
  %27 = mul i64 %26, 4, !dbg !680
  %28 = add i64 0, %27, !dbg !680
  %29 = getelementptr [131 x i32], ptr %1, i64 0, i64 %26, !dbg !680
  %30 = sub i64 528, %28, !dbg !680
  %31 = icmp ult i64 528, %28, !dbg !680
  %32 = icmp ult i64 %30, 4, !dbg !680
  %33 = or i1 %31, %32, !dbg !680
  br i1 %33, label %308, label %34

34:                                               ; preds = %25
  %35 = load i32, ptr %29, align 4, !dbg !680
  %36 = icmp ult i32 %35, 64, !dbg !682
  %37 = zext i1 %36 to i32, !dbg !682
  %38 = load i32, ptr %8, align 4, !dbg !683
  %39 = and i32 %38, %37, !dbg !683
  store i32 %39, ptr %8, align 4, !dbg !683
    #dbg_declare(ptr %10, !684, !DIExpression(), !686)
  store i32 0, ptr %10, align 4, !dbg !686
  br label %40, !dbg !687

40:                                               ; preds = %75, %34
  %41 = load i32, ptr %10, align 4, !dbg !688
  %42 = load i32, ptr %9, align 4, !dbg !690
  %43 = icmp ult i32 %41, %42, !dbg !691
  br i1 %43, label %44, label %83, !dbg !692

44:                                               ; preds = %40
  %45 = load i32, ptr %9, align 4, !dbg !693
  %46 = zext i32 %45 to i64, !dbg !694, !nosanitize !334
  %47 = icmp ult i64 %46, 131, !dbg !694, !nosanitize !334
  br i1 %47, label %50, label %48, !dbg !694, !prof !681, !nosanitize !334

48:                                               ; preds = %44
  %49 = zext i32 %45 to i64, !dbg !694, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @3, i64 %49) #7, !dbg !694, !nosanitize !334
  unreachable, !dbg !694, !nosanitize !334

50:                                               ; preds = %44
  %51 = zext i32 %45 to i64, !dbg !694
  %52 = mul i64 %51, 4, !dbg !694
  %53 = add i64 0, %52, !dbg !694
  %54 = getelementptr [131 x i32], ptr %1, i64 0, i64 %51, !dbg !694
  %55 = sub i64 528, %53, !dbg !694
  %56 = icmp ult i64 528, %53, !dbg !694
  %57 = icmp ult i64 %55, 4, !dbg !694
  %58 = or i1 %56, %57, !dbg !694
  br i1 %58, label %309, label %59

59:                                               ; preds = %50
  %60 = load i32, ptr %54, align 4, !dbg !694
  %61 = load i32, ptr %10, align 4, !dbg !695
  %62 = zext i32 %61 to i64, !dbg !696, !nosanitize !334
  %63 = icmp ult i64 %62, 131, !dbg !696, !nosanitize !334
  br i1 %63, label %66, label %64, !dbg !696, !prof !681, !nosanitize !334

64:                                               ; preds = %59
  %65 = zext i32 %61 to i64, !dbg !696, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @4, i64 %65) #7, !dbg !696, !nosanitize !334
  unreachable, !dbg !696, !nosanitize !334

66:                                               ; preds = %59
  %67 = zext i32 %61 to i64, !dbg !696
  %68 = mul i64 %67, 4, !dbg !696
  %69 = add i64 0, %68, !dbg !696
  %70 = getelementptr [131 x i32], ptr %1, i64 0, i64 %67, !dbg !696
  %71 = sub i64 528, %69, !dbg !696
  %72 = icmp ult i64 528, %69, !dbg !696
  %73 = icmp ult i64 %71, 4, !dbg !696
  %74 = or i1 %72, %73, !dbg !696
  br i1 %74, label %310, label %75

75:                                               ; preds = %66
  %76 = load i32, ptr %70, align 4, !dbg !696
  %77 = icmp ne i32 %60, %76, !dbg !697
  %78 = zext i1 %77 to i32, !dbg !697
  %79 = load i32, ptr %8, align 4, !dbg !698
  %80 = and i32 %79, %78, !dbg !698
  store i32 %80, ptr %8, align 4, !dbg !698
  %81 = load i32, ptr %10, align 4, !dbg !699
  %82 = add i32 %81, 1, !dbg !699
  store i32 %82, ptr %10, align 4, !dbg !699
  br label %40, !dbg !700, !llvm.loop !701

83:                                               ; preds = %40
  %84 = load i32, ptr %9, align 4, !dbg !704
  %85 = zext i32 %84 to i64, !dbg !705, !nosanitize !334
  %86 = icmp ult i64 %85, 131, !dbg !705, !nosanitize !334
  br i1 %86, label %89, label %87, !dbg !705, !prof !681, !nosanitize !334

87:                                               ; preds = %83
  %88 = zext i32 %84 to i64, !dbg !705, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @5, i64 %88) #7, !dbg !705, !nosanitize !334
  unreachable, !dbg !705, !nosanitize !334

89:                                               ; preds = %83
  %90 = zext i32 %84 to i64, !dbg !705
  %91 = mul i64 %90, 4, !dbg !705
  %92 = add i64 0, %91, !dbg !705
  %93 = getelementptr [131 x i32], ptr %1, i64 0, i64 %90, !dbg !705
  %94 = sub i64 528, %92, !dbg !705
  %95 = icmp ult i64 528, %92, !dbg !705
  %96 = icmp ult i64 %94, 4, !dbg !705
  %97 = or i1 %95, %96, !dbg !705
  br i1 %97, label %311, label %98

98:                                               ; preds = %89
  %99 = load i32, ptr %93, align 4, !dbg !705
  %100 = load i32, ptr %9, align 4, !dbg !706
  %101 = zext i32 %100 to i64, !dbg !707, !nosanitize !334
  %102 = icmp ult i64 %101, 64, !dbg !707, !nosanitize !334
  br i1 %102, label %105, label %103, !dbg !707, !prof !681, !nosanitize !334

103:                                              ; preds = %98
  %104 = zext i32 %100 to i64, !dbg !707, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @7, i64 %104) #7, !dbg !707, !nosanitize !334
  unreachable, !dbg !707, !nosanitize !334

105:                                              ; preds = %98
  %106 = zext i32 %100 to i64, !dbg !707
  %107 = mul i64 %106, 4, !dbg !707
  %108 = add i64 0, %107, !dbg !707
  %109 = getelementptr [64 x i32], ptr %3, i64 0, i64 %106, !dbg !707
  %110 = sub i64 256, %108, !dbg !707
  %111 = icmp ult i64 256, %108, !dbg !707
  %112 = icmp ult i64 %110, 4, !dbg !707
  %113 = or i1 %111, %112, !dbg !707
  br i1 %113, label %312, label %114

114:                                              ; preds = %105
  store i32 %99, ptr %109, align 4, !dbg !707
  %115 = load i32, ptr %9, align 4, !dbg !708
  %116 = add i32 64, %115, !dbg !709
  %117 = zext i32 %116 to i64, !dbg !710, !nosanitize !334
  %118 = icmp ult i64 %117, 131, !dbg !710, !nosanitize !334
  br i1 %118, label %121, label %119, !dbg !710, !prof !681, !nosanitize !334

119:                                              ; preds = %114
  %120 = zext i32 %116 to i64, !dbg !710, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @8, i64 %120) #7, !dbg !710, !nosanitize !334
  unreachable, !dbg !710, !nosanitize !334

121:                                              ; preds = %114
  %122 = zext i32 %116 to i64, !dbg !710
  %123 = mul i64 %122, 4, !dbg !710
  %124 = add i64 0, %123, !dbg !710
  %125 = getelementptr [131 x i32], ptr %1, i64 0, i64 %122, !dbg !710
  %126 = sub i64 528, %124, !dbg !710
  %127 = icmp ult i64 528, %124, !dbg !710
  %128 = icmp ult i64 %126, 4, !dbg !710
  %129 = or i1 %127, %128, !dbg !710
  br i1 %129, label %313, label %130

130:                                              ; preds = %121
  %131 = load i32, ptr %125, align 4, !dbg !710
  %132 = load i32, ptr %9, align 4, !dbg !711
  %133 = zext i32 %132 to i64, !dbg !712, !nosanitize !334
  %134 = icmp ult i64 %133, 64, !dbg !712, !nosanitize !334
  br i1 %134, label %137, label %135, !dbg !712, !prof !681, !nosanitize !334

135:                                              ; preds = %130
  %136 = zext i32 %132 to i64, !dbg !712, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @9, i64 %136) #7, !dbg !712, !nosanitize !334
  unreachable, !dbg !712, !nosanitize !334

137:                                              ; preds = %130
  %138 = zext i32 %132 to i64, !dbg !712
  %139 = mul i64 %138, 4, !dbg !712
  %140 = add i64 0, %139, !dbg !712
  %141 = getelementptr [64 x i32], ptr %2, i64 0, i64 %138, !dbg !712
  %142 = sub i64 256, %140, !dbg !712
  %143 = icmp ult i64 256, %140, !dbg !712
  %144 = icmp ult i64 %142, 4, !dbg !712
  %145 = or i1 %143, %144, !dbg !712
  br i1 %145, label %314, label %146

146:                                              ; preds = %137
  store i32 %131, ptr %141, align 4, !dbg !712
  %147 = load i32, ptr %9, align 4, !dbg !713
  %148 = add i32 %147, 1, !dbg !713
  store i32 %148, ptr %9, align 4, !dbg !713
  br label %16, !dbg !714, !llvm.loop !715

149:                                              ; preds = %16
  %150 = load i32, ptr %8, align 4, !dbg !717
  %151 = icmp eq i32 %150, 0, !dbg !718
  %152 = zext i1 %151 to i32, !dbg !718
  %153 = sext i32 %152 to i64, !dbg !717
  call void @klee_assume(i64 noundef %153), !dbg !719
    #dbg_declare(ptr %11, !720, !DIExpression(), !722)
  store i32 0, ptr %11, align 4, !dbg !722
  br label %154, !dbg !723

154:                                              ; preds = %189, %149
  %155 = load i32, ptr %11, align 4, !dbg !724
  %156 = icmp ult i32 %155, 3, !dbg !726
  br i1 %156, label %157, label %192, !dbg !727

157:                                              ; preds = %154
  %158 = load i32, ptr %11, align 4, !dbg !728
  %159 = add i32 128, %158, !dbg !729
  %160 = zext i32 %159 to i64, !dbg !730, !nosanitize !334
  %161 = icmp ult i64 %160, 131, !dbg !730, !nosanitize !334
  br i1 %161, label %164, label %162, !dbg !730, !prof !681, !nosanitize !334

162:                                              ; preds = %157
  %163 = zext i32 %159 to i64, !dbg !730, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @10, i64 %163) #7, !dbg !730, !nosanitize !334
  unreachable, !dbg !730, !nosanitize !334

164:                                              ; preds = %157
  %165 = zext i32 %159 to i64, !dbg !730
  %166 = mul i64 %165, 4, !dbg !730
  %167 = add i64 0, %166, !dbg !730
  %168 = getelementptr [131 x i32], ptr %1, i64 0, i64 %165, !dbg !730
  %169 = sub i64 528, %167, !dbg !730
  %170 = icmp ult i64 528, %167, !dbg !730
  %171 = icmp ult i64 %169, 4, !dbg !730
  %172 = or i1 %170, %171, !dbg !730
  br i1 %172, label %315, label %173

173:                                              ; preds = %164
  %174 = load i32, ptr %168, align 4, !dbg !730
  %175 = load i32, ptr %11, align 4, !dbg !731
  %176 = zext i32 %175 to i64, !dbg !732, !nosanitize !334
  %177 = icmp ult i64 %176, 3, !dbg !732, !nosanitize !334
  br i1 %177, label %180, label %178, !dbg !732, !prof !681, !nosanitize !334

178:                                              ; preds = %173
  %179 = zext i32 %175 to i64, !dbg !732, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @12, i64 %179) #7, !dbg !732, !nosanitize !334
  unreachable, !dbg !732, !nosanitize !334

180:                                              ; preds = %173
  %181 = zext i32 %175 to i64, !dbg !732
  %182 = mul i64 %181, 4, !dbg !732
  %183 = add i64 0, %182, !dbg !732
  %184 = getelementptr [3 x i32], ptr %7, i64 0, i64 %181, !dbg !732
  %185 = sub i64 12, %183, !dbg !732
  %186 = icmp ult i64 12, %183, !dbg !732
  %187 = icmp ult i64 %185, 4, !dbg !732
  %188 = or i1 %186, %187, !dbg !732
  br i1 %188, label %316, label %189

189:                                              ; preds = %180
  store i32 %174, ptr %184, align 4, !dbg !732
  %190 = load i32, ptr %11, align 4, !dbg !733
  %191 = add i32 %190, 1, !dbg !733
  store i32 %191, ptr %11, align 4, !dbg !733
  br label %154, !dbg !734, !llvm.loop !735

192:                                              ; preds = %154
    #dbg_declare(ptr %12, !737, !DIExpression(), !738)
  %193 = getelementptr inbounds [64 x i32], ptr %2, i64 0, i64 0, !dbg !739
  %194 = getelementptr inbounds [64 x i32], ptr %3, i64 0, i64 0, !dbg !740
  %195 = getelementptr inbounds [64 x i32], ptr %4, i64 0, i64 0, !dbg !741
  %196 = getelementptr inbounds [64 x i32], ptr %5, i64 0, i64 0, !dbg !742
  %197 = getelementptr inbounds [128 x i32], ptr %6, i64 0, i64 0, !dbg !743
  %198 = getelementptr inbounds [3 x i32], ptr %7, i64 0, i64 0, !dbg !744
  %199 = call i32 @permute(i32 noundef 64, ptr noundef %193, ptr noundef %194, ptr noundef %195, ptr noundef %196, ptr noundef %197, ptr noundef %198), !dbg !745
  store i32 %199, ptr %12, align 4, !dbg !738
  %200 = load i32, ptr %12, align 4, !dbg !746
  %201 = icmp eq i32 %200, 2, !dbg !746
  br i1 %201, label %203, label %202, !dbg !746

202:                                              ; preds = %192
  call void @klee_assert_fail(ptr noundef @.str.1, ptr noundef @.src, i32 noundef 37, ptr noundef @__PRETTY_FUNCTION__.checked_main) #8, !dbg !746
  unreachable, !dbg !746

203:                                              ; preds = %192
    #dbg_declare(ptr %13, !747, !DIExpression(), !749)
  store i32 0, ptr %13, align 4, !dbg !749
  br label %204, !dbg !750

204:                                              ; preds = %278, %203
  %205 = load i32, ptr %13, align 4, !dbg !751
  %206 = icmp ult i32 %205, 64, !dbg !753
  br i1 %206, label %207, label %281, !dbg !754

207:                                              ; preds = %204
  %208 = load i32, ptr %13, align 4, !dbg !755
  %209 = zext i32 %208 to i64, !dbg !755, !nosanitize !334
  %210 = icmp ult i64 %209, 64, !dbg !755, !nosanitize !334
  br i1 %210, label %213, label %211, !dbg !755, !prof !681, !nosanitize !334

211:                                              ; preds = %207
  %212 = zext i32 %208 to i64, !dbg !755, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @13, i64 %212) #7, !dbg !755, !nosanitize !334
  unreachable, !dbg !755, !nosanitize !334

213:                                              ; preds = %207
  %214 = zext i32 %208 to i64, !dbg !755
  %215 = mul i64 %214, 4, !dbg !755
  %216 = add i64 0, %215, !dbg !755
  %217 = getelementptr [64 x i32], ptr %3, i64 0, i64 %214, !dbg !755
  %218 = sub i64 256, %216, !dbg !755
  %219 = icmp ult i64 256, %216, !dbg !755
  %220 = icmp ult i64 %218, 4, !dbg !755
  %221 = or i1 %219, %220, !dbg !755
  br i1 %221, label %317, label %222

222:                                              ; preds = %213
  %223 = load i32, ptr %217, align 4, !dbg !755
  %224 = load i32, ptr %13, align 4, !dbg !755
  %225 = zext i32 %224 to i64, !dbg !755, !nosanitize !334
  %226 = icmp ult i64 %225, 131, !dbg !755, !nosanitize !334
  br i1 %226, label %229, label %227, !dbg !755, !prof !681, !nosanitize !334

227:                                              ; preds = %222
  %228 = zext i32 %224 to i64, !dbg !755, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @14, i64 %228) #7, !dbg !755, !nosanitize !334
  unreachable, !dbg !755, !nosanitize !334

229:                                              ; preds = %222
  %230 = zext i32 %224 to i64, !dbg !755
  %231 = mul i64 %230, 4, !dbg !755
  %232 = add i64 0, %231, !dbg !755
  %233 = getelementptr [131 x i32], ptr %1, i64 0, i64 %230, !dbg !755
  %234 = sub i64 528, %232, !dbg !755
  %235 = icmp ult i64 528, %232, !dbg !755
  %236 = icmp ult i64 %234, 4, !dbg !755
  %237 = or i1 %235, %236, !dbg !755
  br i1 %237, label %318, label %238

238:                                              ; preds = %229
  %239 = load i32, ptr %233, align 4, !dbg !755
  %240 = icmp eq i32 %223, %239, !dbg !755
  br i1 %240, label %242, label %241, !dbg !755

241:                                              ; preds = %238
  call void @klee_assert_fail(ptr noundef @.str.2, ptr noundef @.src, i32 noundef 39, ptr noundef @__PRETTY_FUNCTION__.checked_main) #8, !dbg !755
  unreachable, !dbg !755

242:                                              ; preds = %238
  %243 = load i32, ptr %13, align 4, !dbg !757
  %244 = zext i32 %243 to i64, !dbg !757, !nosanitize !334
  %245 = icmp ult i64 %244, 64, !dbg !757, !nosanitize !334
  br i1 %245, label %248, label %246, !dbg !757, !prof !681, !nosanitize !334

246:                                              ; preds = %242
  %247 = zext i32 %243 to i64, !dbg !757, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @15, i64 %247) #7, !dbg !757, !nosanitize !334
  unreachable, !dbg !757, !nosanitize !334

248:                                              ; preds = %242
  %249 = zext i32 %243 to i64, !dbg !757
  %250 = mul i64 %249, 4, !dbg !757
  %251 = add i64 0, %250, !dbg !757
  %252 = getelementptr [64 x i32], ptr %2, i64 0, i64 %249, !dbg !757
  %253 = sub i64 256, %251, !dbg !757
  %254 = icmp ult i64 256, %251, !dbg !757
  %255 = icmp ult i64 %253, 4, !dbg !757
  %256 = or i1 %254, %255, !dbg !757
  br i1 %256, label %319, label %257

257:                                              ; preds = %248
  %258 = load i32, ptr %252, align 4, !dbg !757
  %259 = load i32, ptr %13, align 4, !dbg !757
  %260 = add i32 64, %259, !dbg !757
  %261 = zext i32 %260 to i64, !dbg !757, !nosanitize !334
  %262 = icmp ult i64 %261, 131, !dbg !757, !nosanitize !334
  br i1 %262, label %265, label %263, !dbg !757, !prof !681, !nosanitize !334

263:                                              ; preds = %257
  %264 = zext i32 %260 to i64, !dbg !757, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @16, i64 %264) #7, !dbg !757, !nosanitize !334
  unreachable, !dbg !757, !nosanitize !334

265:                                              ; preds = %257
  %266 = zext i32 %260 to i64, !dbg !757
  %267 = mul i64 %266, 4, !dbg !757
  %268 = add i64 0, %267, !dbg !757
  %269 = getelementptr [131 x i32], ptr %1, i64 0, i64 %266, !dbg !757
  %270 = sub i64 528, %268, !dbg !757
  %271 = icmp ult i64 528, %268, !dbg !757
  %272 = icmp ult i64 %270, 4, !dbg !757
  %273 = or i1 %271, %272, !dbg !757
  br i1 %273, label %320, label %274

274:                                              ; preds = %265
  %275 = load i32, ptr %269, align 4, !dbg !757
  %276 = icmp eq i32 %258, %275, !dbg !757
  br i1 %276, label %278, label %277, !dbg !757

277:                                              ; preds = %274
  call void @klee_assert_fail(ptr noundef @.str.3, ptr noundef @.src, i32 noundef 40, ptr noundef @__PRETTY_FUNCTION__.checked_main) #8, !dbg !757
  unreachable, !dbg !757

278:                                              ; preds = %274
  %279 = load i32, ptr %13, align 4, !dbg !758
  %280 = add i32 %279, 1, !dbg !758
  store i32 %280, ptr %13, align 4, !dbg !758
  br label %204, !dbg !759, !llvm.loop !760

281:                                              ; preds = %204
    #dbg_declare(ptr %14, !762, !DIExpression(), !764)
  store i32 0, ptr %14, align 4, !dbg !764
  br label %282, !dbg !765

282:                                              ; preds = %304, %281
  %283 = load i32, ptr %14, align 4, !dbg !766
  %284 = icmp ult i32 %283, 3, !dbg !768
  br i1 %284, label %285, label %307, !dbg !769

285:                                              ; preds = %282
  %286 = load i32, ptr %14, align 4, !dbg !770
  %287 = zext i32 %286 to i64, !dbg !770, !nosanitize !334
  %288 = icmp ult i64 %287, 3, !dbg !770, !nosanitize !334
  br i1 %288, label %291, label %289, !dbg !770, !prof !681, !nosanitize !334

289:                                              ; preds = %285
  %290 = zext i32 %286 to i64, !dbg !770, !nosanitize !334
  call void @__ubsan_handle_out_of_bounds_abort(ptr @17, i64 %290) #7, !dbg !770, !nosanitize !334
  unreachable, !dbg !770, !nosanitize !334

291:                                              ; preds = %285
  %292 = zext i32 %286 to i64, !dbg !770
  %293 = mul i64 %292, 4, !dbg !770
  %294 = add i64 0, %293, !dbg !770
  %295 = getelementptr [3 x i32], ptr %7, i64 0, i64 %292, !dbg !770
  %296 = sub i64 12, %294, !dbg !770
  %297 = icmp ult i64 12, %294, !dbg !770
  %298 = icmp ult i64 %296, 4, !dbg !770
  %299 = or i1 %297, %298, !dbg !770
  br i1 %299, label %321, label %300

300:                                              ; preds = %291
  %301 = load i32, ptr %295, align 4, !dbg !770
  %302 = icmp eq i32 %301, 0, !dbg !770
  br i1 %302, label %304, label %303, !dbg !770

303:                                              ; preds = %300
  call void @klee_assert_fail(ptr noundef @.str.4, ptr noundef @.src, i32 noundef 44, ptr noundef @__PRETTY_FUNCTION__.checked_main) #8, !dbg !770
  unreachable, !dbg !770

304:                                              ; preds = %300
  %305 = load i32, ptr %14, align 4, !dbg !771
  %306 = add i32 %305, 1, !dbg !771
  store i32 %306, ptr %14, align 4, !dbg !771
  br label %282, !dbg !772, !llvm.loop !773

307:                                              ; preds = %282
  ret i32 0, !dbg !775

308:                                              ; preds = %25
  call void @abort(), !dbg !680
  unreachable, !dbg !680

309:                                              ; preds = %50
  call void @abort(), !dbg !694
  unreachable, !dbg !694

310:                                              ; preds = %66
  call void @abort(), !dbg !696
  unreachable, !dbg !696

311:                                              ; preds = %89
  call void @abort(), !dbg !705
  unreachable, !dbg !705

312:                                              ; preds = %105
  call void @abort(), !dbg !707
  unreachable, !dbg !707

313:                                              ; preds = %121
  call void @abort(), !dbg !710
  unreachable, !dbg !710

314:                                              ; preds = %137
  call void @abort(), !dbg !712
  unreachable, !dbg !712

315:                                              ; preds = %164
  call void @abort(), !dbg !730
  unreachable, !dbg !730

316:                                              ; preds = %180
  call void @abort(), !dbg !732
  unreachable, !dbg !732

317:                                              ; preds = %213
  call void @abort(), !dbg !755
  unreachable, !dbg !755

318:                                              ; preds = %229
  call void @abort(), !dbg !755
  unreachable, !dbg !755

319:                                              ; preds = %248
  call void @abort(), !dbg !757
  unreachable, !dbg !757

320:                                              ; preds = %265
  call void @abort(), !dbg !757
  unreachable, !dbg !757

321:                                              ; preds = %291
  call void @abort(), !dbg !770
  unreachable, !dbg !770
}

declare void @klee_make_symbolic(ptr noundef, i64 noundef, ptr noundef) #1

declare void @klee_assume(i64 noundef) #1

; Function Attrs: noreturn
declare void @klee_assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2

; Function Attrs: noinline nounwind sspstrong uwtable
define i32 @main() #3 !dbg !776 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i8, align 1
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !777, !DIExpression(), !778)
  %4 = call i32 @checked_main(), !dbg !779
  store i32 %4, ptr %2, align 4, !dbg !778
    #dbg_declare(ptr %3, !780, !DIExpression(), !782)
  call void @klee_make_symbolic(ptr noundef %3, i64 noundef 1, ptr noundef @.str.5), !dbg !783
  %5 = load i32, ptr %2, align 4, !dbg !784
  ret i32 %5, !dbg !785
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_type_mismatch_v1(ptr noundef %0, i64 noundef %1) #4 !dbg !786 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !799, !DIExpression(), !800)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !801, !DIExpression(), !802)
  %5 = load ptr, ptr %3, align 8, !dbg !803
  %6 = load i64, ptr %4, align 8, !dbg !804
  call void @_ZN7__ubsanL22handleTypeMismatchImplEP16TypeMismatchDatam(ptr noundef %5, i64 noundef %6), !dbg !805
  ret void, !dbg !806
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL22handleTypeMismatchImplEP16TypeMismatchDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !807 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i64, align 8
  %6 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !808, !DIExpression(), !809)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !810, !DIExpression(), !811)
    #dbg_declare(ptr %5, !812, !DIExpression(), !813)
  %7 = load ptr, ptr %3, align 8, !dbg !814
  %8 = getelementptr inbounds %struct.TypeMismatchData, ptr %7, i32 0, i32 2, !dbg !815
  %9 = load i8, ptr %8, align 8, !dbg !815
  %10 = zext i8 %9 to i32, !dbg !814
  %11 = zext i32 %10 to i64, !dbg !816
  call void @klee_overshift_check(i64 64, i64 %11), !dbg !816
  %12 = shl i64 1, %11, !dbg !816, !klee.check.shift !817
  store i64 %12, ptr %5, align 8, !dbg !813
    #dbg_declare(ptr %6, !818, !DIExpression(), !819)
  %13 = load i64, ptr %4, align 8, !dbg !820
  %14 = icmp ne i64 %13, 0, !dbg !820
  br i1 %14, label %23, label %15, !dbg !822

15:                                               ; preds = %2
  %16 = load ptr, ptr %3, align 8, !dbg !823
  %17 = getelementptr inbounds %struct.TypeMismatchData, ptr %16, i32 0, i32 3, !dbg !824
  %18 = load i8, ptr %17, align 1, !dbg !824
  %19 = zext i8 %18 to i32, !dbg !823
  %20 = icmp eq i32 %19, 10, !dbg !825
  %21 = zext i1 %20 to i64, !dbg !826
  %22 = select i1 %20, i32 2, i32 1, !dbg !826
  store i32 %22, ptr %6, align 4, !dbg !827
  br label %31, !dbg !828

23:                                               ; preds = %2
  %24 = load i64, ptr %4, align 8, !dbg !829
  %25 = load i64, ptr %5, align 8, !dbg !831
  %26 = sub i64 %25, 1, !dbg !832
  %27 = and i64 %24, %26, !dbg !833
  %28 = icmp ne i64 %27, 0, !dbg !829
  br i1 %28, label %29, label %30, !dbg !834

29:                                               ; preds = %23
  store i32 7, ptr %6, align 4, !dbg !835
  br label %31, !dbg !836

30:                                               ; preds = %23
  store i32 9, ptr %6, align 4, !dbg !837
  br label %31

31:                                               ; preds = %29, %30, %15
  %32 = load i32, ptr %6, align 4, !dbg !838
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %32) #8, !dbg !839
  unreachable, !dbg !839
}

; Function Attrs: mustprogress noinline noreturn sspstrong uwtable
define internal void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %0) #5 !dbg !840 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !843, !DIExpression(), !844)
  %3 = load i32, ptr %2, align 4, !dbg !845
  %4 = call noundef ptr @_ZN7__ubsanL19ConvertTypeToStringENS_9ErrorTypeE(i32 noundef %3), !dbg !846
  %5 = load i32, ptr %2, align 4, !dbg !847
  %6 = call noundef ptr @_ZN7__ubsanL10get_suffixENS_9ErrorTypeE(i32 noundef %5), !dbg !848
  call void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef %4, ptr noundef %6) #8, !dbg !849
  unreachable, !dbg !849
}

; Function Attrs: mustprogress noinline nounwind sspstrong uwtable
define internal noundef ptr @_ZN7__ubsanL19ConvertTypeToStringENS_9ErrorTypeE(i32 noundef %0) #6 !dbg !850 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store i32 %0, ptr %3, align 4
    #dbg_declare(ptr %3, !853, !DIExpression(), !854)
  %4 = load i32, ptr %3, align 4, !dbg !855
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
  ], !dbg !856

5:                                                ; preds = %1
  store ptr @.str.4.2, ptr %2, align 8, !dbg !857
  br label %42, !dbg !857

6:                                                ; preds = %1
  store ptr @.str.5.3, ptr %2, align 8, !dbg !860
  br label %42, !dbg !860

7:                                                ; preds = %1
  store ptr @.str.5.3, ptr %2, align 8, !dbg !861
  br label %42, !dbg !861

8:                                                ; preds = %1
  store ptr @.str.6, ptr %2, align 8, !dbg !862
  br label %42, !dbg !862

9:                                                ; preds = %1
  store ptr @.str.7, ptr %2, align 8, !dbg !863
  br label %42, !dbg !863

10:                                               ; preds = %1
  store ptr @.str.8, ptr %2, align 8, !dbg !864
  br label %42, !dbg !864

11:                                               ; preds = %1
  store ptr @.str.9, ptr %2, align 8, !dbg !865
  br label %42, !dbg !865

12:                                               ; preds = %1
  store ptr @.str.10, ptr %2, align 8, !dbg !866
  br label %42, !dbg !866

13:                                               ; preds = %1
  store ptr @.str.11, ptr %2, align 8, !dbg !867
  br label %42, !dbg !867

14:                                               ; preds = %1
  store ptr @.str.12, ptr %2, align 8, !dbg !868
  br label %42, !dbg !868

15:                                               ; preds = %1
  store ptr @.str.13, ptr %2, align 8, !dbg !869
  br label %42, !dbg !869

16:                                               ; preds = %1
  store ptr @.str.14, ptr %2, align 8, !dbg !870
  br label %42, !dbg !870

17:                                               ; preds = %1
  store ptr @.str.15, ptr %2, align 8, !dbg !871
  br label %42, !dbg !871

18:                                               ; preds = %1
  store ptr @.str.16, ptr %2, align 8, !dbg !872
  br label %42, !dbg !872

19:                                               ; preds = %1
  store ptr @.str.17, ptr %2, align 8, !dbg !873
  br label %42, !dbg !873

20:                                               ; preds = %1
  store ptr @.str.18, ptr %2, align 8, !dbg !874
  br label %42, !dbg !874

21:                                               ; preds = %1
  store ptr @.str.19, ptr %2, align 8, !dbg !875
  br label %42, !dbg !875

22:                                               ; preds = %1
  store ptr @.str.20, ptr %2, align 8, !dbg !876
  br label %42, !dbg !876

23:                                               ; preds = %1
  store ptr @.str.21, ptr %2, align 8, !dbg !877
  br label %42, !dbg !877

24:                                               ; preds = %1
  store ptr @.str.22, ptr %2, align 8, !dbg !878
  br label %42, !dbg !878

25:                                               ; preds = %1
  store ptr @.str.23, ptr %2, align 8, !dbg !879
  br label %42, !dbg !879

26:                                               ; preds = %1
  store ptr @.str.24, ptr %2, align 8, !dbg !880
  br label %42, !dbg !880

27:                                               ; preds = %1
  store ptr @.str.25, ptr %2, align 8, !dbg !881
  br label %42, !dbg !881

28:                                               ; preds = %1
  store ptr @.str.26, ptr %2, align 8, !dbg !882
  br label %42, !dbg !882

29:                                               ; preds = %1
  store ptr @.str.27, ptr %2, align 8, !dbg !883
  br label %42, !dbg !883

30:                                               ; preds = %1
  store ptr @.str.28, ptr %2, align 8, !dbg !884
  br label %42, !dbg !884

31:                                               ; preds = %1
  store ptr @.str.29, ptr %2, align 8, !dbg !885
  br label %42, !dbg !885

32:                                               ; preds = %1
  store ptr @.str.30, ptr %2, align 8, !dbg !886
  br label %42, !dbg !886

33:                                               ; preds = %1
  store ptr @.str.31, ptr %2, align 8, !dbg !887
  br label %42, !dbg !887

34:                                               ; preds = %1
  store ptr @.str.32, ptr %2, align 8, !dbg !888
  br label %42, !dbg !888

35:                                               ; preds = %1
  store ptr @.str.33, ptr %2, align 8, !dbg !889
  br label %42, !dbg !889

36:                                               ; preds = %1
  store ptr @.str.33, ptr %2, align 8, !dbg !890
  br label %42, !dbg !890

37:                                               ; preds = %1
  store ptr @.str.34, ptr %2, align 8, !dbg !891
  br label %42, !dbg !891

38:                                               ; preds = %1
  store ptr @.str.34, ptr %2, align 8, !dbg !892
  br label %42, !dbg !892

39:                                               ; preds = %1
  store ptr @.str.35, ptr %2, align 8, !dbg !893
  br label %42, !dbg !893

40:                                               ; preds = %1
  store ptr @.str.36, ptr %2, align 8, !dbg !894
  br label %42, !dbg !894

41:                                               ; preds = %1
  call void @abort(), !dbg !895
  unreachable, !dbg !895

42:                                               ; preds = %40, %39, %38, %37, %36, %35, %34, %33, %32, %31, %30, %29, %28, %27, %26, %25, %24, %23, %22, %21, %20, %19, %18, %17, %16, %15, %14, %13, %12, %11, %10, %9, %8, %7, %6, %5
  %43 = load ptr, ptr %2, align 8, !dbg !897
  ret ptr %43, !dbg !897
}

; Function Attrs: mustprogress noinline nounwind sspstrong uwtable
define internal noundef ptr @_ZN7__ubsanL10get_suffixENS_9ErrorTypeE(i32 noundef %0) #6 !dbg !898 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store i32 %0, ptr %3, align 4
    #dbg_declare(ptr %3, !899, !DIExpression(), !900)
  %4 = load i32, ptr %3, align 4, !dbg !901
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
  ], !dbg !902

5:                                                ; preds = %1
  store ptr @.str.37, ptr %2, align 8, !dbg !903
  br label %25, !dbg !903

6:                                                ; preds = %1, %1, %1, %1, %1, %1, %1, %1
  store ptr @.str.38, ptr %2, align 8, !dbg !905
  br label %25, !dbg !905

7:                                                ; preds = %1
  store ptr @.str.38, ptr %2, align 8, !dbg !906
  br label %25, !dbg !906

8:                                                ; preds = %1, %1
  store ptr @.str.39, ptr %2, align 8, !dbg !907
  br label %25, !dbg !907

9:                                                ; preds = %1, %1
  store ptr @.str.40, ptr %2, align 8, !dbg !908
  br label %25, !dbg !908

10:                                               ; preds = %1
  store ptr @.str.41, ptr %2, align 8, !dbg !909
  br label %25, !dbg !909

11:                                               ; preds = %1
  store ptr @.str.37, ptr %2, align 8, !dbg !910
  br label %25, !dbg !910

12:                                               ; preds = %1, %1
  store ptr @.str.42, ptr %2, align 8, !dbg !911
  br label %25, !dbg !911

13:                                               ; preds = %1, %1
  store ptr @.str.43, ptr %2, align 8, !dbg !912
  br label %25, !dbg !912

14:                                               ; preds = %1, %1
  store ptr @.str.39, ptr %2, align 8, !dbg !913
  br label %25, !dbg !913

15:                                               ; preds = %1
  store ptr @.str.38, ptr %2, align 8, !dbg !914
  br label %25, !dbg !914

16:                                               ; preds = %1
  store ptr @.str.44, ptr %2, align 8, !dbg !915
  br label %25, !dbg !915

17:                                               ; preds = %1
  store ptr @.str.45, ptr %2, align 8, !dbg !916
  br label %25, !dbg !916

18:                                               ; preds = %1
  store ptr @.str.38, ptr %2, align 8, !dbg !917
  br label %25, !dbg !917

19:                                               ; preds = %1
  store ptr @.str.39, ptr %2, align 8, !dbg !918
  br label %25, !dbg !918

20:                                               ; preds = %1, %1
  store ptr @.str.46, ptr %2, align 8, !dbg !919
  br label %25, !dbg !919

21:                                               ; preds = %1
  store ptr @.str.47, ptr %2, align 8, !dbg !920
  br label %25, !dbg !920

22:                                               ; preds = %1, %1, %1, %1
  store ptr @.str.48, ptr %2, align 8, !dbg !921
  br label %25, !dbg !921

23:                                               ; preds = %1, %1
  store ptr @.str.37, ptr %2, align 8, !dbg !922
  br label %25, !dbg !922

24:                                               ; preds = %1
  store ptr @.str.37, ptr %2, align 8, !dbg !923
  br label %25, !dbg !923

25:                                               ; preds = %24, %23, %22, %21, %20, %19, %18, %17, %16, %15, %14, %13, %12, %11, %10, %9, %8, %7, %6, %5
  %26 = load ptr, ptr %2, align 8, !dbg !924
  ret ptr %26, !dbg !924
}

; Function Attrs: mustprogress noinline noreturn sspstrong uwtable
define internal void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef %0, ptr noundef %1) #5 !dbg !925 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !928, !DIExpression(), !929)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !930, !DIExpression(), !931)
  %5 = load ptr, ptr %3, align 8, !dbg !932
  %6 = load ptr, ptr %4, align 8, !dbg !933
  call void @klee_report_error(ptr noundef @.str.3.1, i32 noundef 37, ptr noundef %5, ptr noundef %6) #8, !dbg !934
  unreachable, !dbg !934
}

; Function Attrs: noreturn
declare void @klee_report_error(ptr noundef, i32 noundef, ptr noundef, ptr noundef) #2

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_type_mismatch_v1_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !935 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !936, !DIExpression(), !937)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !938, !DIExpression(), !939)
  %5 = load ptr, ptr %3, align 8, !dbg !940
  %6 = load i64, ptr %4, align 8, !dbg !941
  call void @_ZN7__ubsanL22handleTypeMismatchImplEP16TypeMismatchDatam(ptr noundef %5, i64 noundef %6), !dbg !942
  ret void, !dbg !943
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_alignment_assumption(ptr noundef %0, i64 noundef %1, i64 noundef %2, i64 noundef %3) #4 !dbg !944 {
  %5 = alloca ptr, align 8
  %6 = alloca i64, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  store ptr %0, ptr %5, align 8
    #dbg_declare(ptr %5, !949, !DIExpression(), !950)
  store i64 %1, ptr %6, align 8
    #dbg_declare(ptr %6, !951, !DIExpression(), !952)
  store i64 %2, ptr %7, align 8
    #dbg_declare(ptr %7, !953, !DIExpression(), !954)
  store i64 %3, ptr %8, align 8
    #dbg_declare(ptr %8, !955, !DIExpression(), !956)
  %9 = load ptr, ptr %5, align 8, !dbg !957
  %10 = load i64, ptr %6, align 8, !dbg !958
  %11 = load i64, ptr %7, align 8, !dbg !959
  %12 = load i64, ptr %8, align 8, !dbg !960
  call void @_ZN7__ubsanL29handleAlignmentAssumptionImplEP23AlignmentAssumptionDatammm(ptr noundef %9, i64 noundef %10, i64 noundef %11, i64 noundef %12), !dbg !961
  ret void, !dbg !962
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL29handleAlignmentAssumptionImplEP23AlignmentAssumptionDatammm(ptr noundef %0, i64 noundef %1, i64 noundef %2, i64 noundef %3) #4 !dbg !963 {
  %5 = alloca ptr, align 8
  %6 = alloca i64, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  %9 = alloca i32, align 4
  store ptr %0, ptr %5, align 8
    #dbg_declare(ptr %5, !964, !DIExpression(), !965)
  store i64 %1, ptr %6, align 8
    #dbg_declare(ptr %6, !966, !DIExpression(), !967)
  store i64 %2, ptr %7, align 8
    #dbg_declare(ptr %7, !968, !DIExpression(), !969)
  store i64 %3, ptr %8, align 8
    #dbg_declare(ptr %8, !970, !DIExpression(), !971)
    #dbg_declare(ptr %9, !972, !DIExpression(), !973)
  store i32 8, ptr %9, align 4, !dbg !973
  %10 = load i32, ptr %9, align 4, !dbg !974
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %10) #8, !dbg !975
  unreachable, !dbg !975
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_alignment_assumption_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2, i64 noundef %3) #4 !dbg !976 {
  %5 = alloca ptr, align 8
  %6 = alloca i64, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  store ptr %0, ptr %5, align 8
    #dbg_declare(ptr %5, !977, !DIExpression(), !978)
  store i64 %1, ptr %6, align 8
    #dbg_declare(ptr %6, !979, !DIExpression(), !980)
  store i64 %2, ptr %7, align 8
    #dbg_declare(ptr %7, !981, !DIExpression(), !982)
  store i64 %3, ptr %8, align 8
    #dbg_declare(ptr %8, !983, !DIExpression(), !984)
  %9 = load ptr, ptr %5, align 8, !dbg !985
  %10 = load i64, ptr %6, align 8, !dbg !986
  %11 = load i64, ptr %7, align 8, !dbg !987
  %12 = load i64, ptr %8, align 8, !dbg !988
  call void @_ZN7__ubsanL29handleAlignmentAssumptionImplEP23AlignmentAssumptionDatammm(ptr noundef %9, i64 noundef %10, i64 noundef %11, i64 noundef %12), !dbg !989
  ret void, !dbg !990
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_add_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !991 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !999, !DIExpression(), !1000)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1001, !DIExpression(), !1000)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1002, !DIExpression(), !1000)
  %7 = load ptr, ptr %4, align 8, !dbg !1000
  %8 = load i64, ptr %5, align 8, !dbg !1000
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.49), !dbg !1000
  ret void, !dbg !1000
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %0, i64 noundef %1, ptr noundef %2) #4 !dbg !1003 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca ptr, align 8
  %7 = alloca i8, align 1
  %8 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1006, !DIExpression(), !1007)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1008, !DIExpression(), !1009)
  store ptr %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1010, !DIExpression(), !1011)
    #dbg_declare(ptr %7, !1012, !DIExpression(), !1013)
  %9 = load ptr, ptr %4, align 8, !dbg !1014
  %10 = getelementptr inbounds %struct.OverflowData, ptr %9, i32 0, i32 1, !dbg !1015
  %11 = load ptr, ptr %10, align 8, !dbg !1015
  %12 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %11), !dbg !1016
  %13 = zext i1 %12 to i8, !dbg !1013
  store i8 %13, ptr %7, align 1, !dbg !1013
    #dbg_declare(ptr %8, !1017, !DIExpression(), !1018)
  %14 = load i8, ptr %7, align 1, !dbg !1019
  %15 = trunc i8 %14 to i1, !dbg !1019
  %16 = zext i1 %15 to i64, !dbg !1019
  %17 = select i1 %15, i32 10, i32 11, !dbg !1019
  store i32 %17, ptr %8, align 4, !dbg !1018
  %18 = load i32, ptr %8, align 4, !dbg !1020
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %18) #8, !dbg !1021
  unreachable, !dbg !1021
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define linkonce_odr noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %0) #4 comdat align 2 !dbg !1022 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1023, !DIExpression(), !1025)
  %3 = load ptr, ptr %2, align 8
  %4 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %3), !dbg !1026
  br i1 %4, label %5, label %11, !dbg !1027

5:                                                ; preds = %1
  %6 = getelementptr inbounds %"class.__ubsan::TypeDescriptor", ptr %3, i32 0, i32 1, !dbg !1028
  %7 = load i16, ptr %6, align 2, !dbg !1028
  %8 = zext i16 %7 to i32, !dbg !1028
  %9 = and i32 %8, 1, !dbg !1029
  %10 = icmp ne i32 %9, 0, !dbg !1030
  br label %11

11:                                               ; preds = %5, %1
  %12 = phi i1 [ false, %1 ], [ %10, %5 ], !dbg !1025
  ret i1 %12, !dbg !1031
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define linkonce_odr noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %0) #4 comdat align 2 !dbg !1032 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1033, !DIExpression(), !1034)
  %3 = load ptr, ptr %2, align 8
  %4 = call noundef i32 @_ZNK7__ubsan14TypeDescriptor7getKindEv(ptr noundef nonnull align 2 dereferenceable(5) %3), !dbg !1035
  %5 = icmp eq i32 %4, 0, !dbg !1036
  ret i1 %5, !dbg !1037
}

; Function Attrs: mustprogress noinline nounwind sspstrong uwtable
define linkonce_odr noundef i32 @_ZNK7__ubsan14TypeDescriptor7getKindEv(ptr noundef nonnull align 2 dereferenceable(5) %0) #6 comdat align 2 !dbg !1038 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1039, !DIExpression(), !1040)
  %3 = load ptr, ptr %2, align 8
  %4 = getelementptr inbounds %"class.__ubsan::TypeDescriptor", ptr %3, i32 0, i32 0, !dbg !1041
  %5 = load i16, ptr %4, align 2, !dbg !1041
  %6 = zext i16 %5 to i32, !dbg !1042
  ret i32 %6, !dbg !1043
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_add_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1044 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1045, !DIExpression(), !1046)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1047, !DIExpression(), !1046)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1048, !DIExpression(), !1046)
  %7 = load ptr, ptr %4, align 8, !dbg !1046
  %8 = load i64, ptr %5, align 8, !dbg !1046
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.49), !dbg !1046
  ret void, !dbg !1046
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_sub_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1049 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1050, !DIExpression(), !1051)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1052, !DIExpression(), !1051)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1053, !DIExpression(), !1051)
  %7 = load ptr, ptr %4, align 8, !dbg !1051
  %8 = load i64, ptr %5, align 8, !dbg !1051
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.1.50), !dbg !1051
  ret void, !dbg !1051
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_sub_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1054 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1055, !DIExpression(), !1056)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1057, !DIExpression(), !1056)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1058, !DIExpression(), !1056)
  %7 = load ptr, ptr %4, align 8, !dbg !1056
  %8 = load i64, ptr %5, align 8, !dbg !1056
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.1.50), !dbg !1056
  ret void, !dbg !1056
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_mul_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1059 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1060, !DIExpression(), !1061)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1062, !DIExpression(), !1061)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1063, !DIExpression(), !1061)
  %7 = load ptr, ptr %4, align 8, !dbg !1061
  %8 = load i64, ptr %5, align 8, !dbg !1061
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.2.51), !dbg !1061
  ret void, !dbg !1061
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_mul_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1064 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1065, !DIExpression(), !1066)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1067, !DIExpression(), !1066)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1068, !DIExpression(), !1066)
  %7 = load ptr, ptr %4, align 8, !dbg !1066
  %8 = load i64, ptr %5, align 8, !dbg !1066
  call void @_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc(ptr noundef %7, i64 noundef %8, ptr noundef @.str.2.51), !dbg !1066
  ret void, !dbg !1066
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_negate_overflow(ptr noundef %0, i64 noundef %1) #4 !dbg !1069 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1072, !DIExpression(), !1073)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1074, !DIExpression(), !1075)
  %5 = load ptr, ptr %3, align 8, !dbg !1076
  %6 = load i64, ptr %4, align 8, !dbg !1077
  call void @_ZN7__ubsanL24handleNegateOverflowImplEP12OverflowDatam(ptr noundef %5, i64 noundef %6), !dbg !1078
  ret void, !dbg !1079
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL24handleNegateOverflowImplEP12OverflowDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1080 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i8, align 1
  %6 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1081, !DIExpression(), !1082)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1083, !DIExpression(), !1084)
    #dbg_declare(ptr %5, !1085, !DIExpression(), !1086)
  %7 = load ptr, ptr %3, align 8, !dbg !1087
  %8 = getelementptr inbounds %struct.OverflowData, ptr %7, i32 0, i32 1, !dbg !1088
  %9 = load ptr, ptr %8, align 8, !dbg !1088
  %10 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %9), !dbg !1089
  %11 = zext i1 %10 to i8, !dbg !1086
  store i8 %11, ptr %5, align 1, !dbg !1086
    #dbg_declare(ptr %6, !1090, !DIExpression(), !1091)
  %12 = load i8, ptr %5, align 1, !dbg !1092
  %13 = trunc i8 %12 to i1, !dbg !1092
  %14 = zext i1 %13 to i64, !dbg !1092
  %15 = select i1 %13, i32 10, i32 11, !dbg !1092
  store i32 %15, ptr %6, align 4, !dbg !1091
  %16 = load i32, ptr %6, align 4, !dbg !1093
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %16) #8, !dbg !1094
  unreachable, !dbg !1094
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_negate_overflow_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1095 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1096, !DIExpression(), !1097)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1098, !DIExpression(), !1099)
  %5 = load ptr, ptr %3, align 8, !dbg !1100
  %6 = load i64, ptr %4, align 8, !dbg !1101
  call void @_ZN7__ubsanL24handleNegateOverflowImplEP12OverflowDatam(ptr noundef %5, i64 noundef %6), !dbg !1102
  ret void, !dbg !1103
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_divrem_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1104 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1105, !DIExpression(), !1106)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1107, !DIExpression(), !1108)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1109, !DIExpression(), !1110)
  %7 = load ptr, ptr %4, align 8, !dbg !1111
  %8 = load i64, ptr %5, align 8, !dbg !1112
  %9 = load i64, ptr %6, align 8, !dbg !1113
  call void @_ZN7__ubsanL24handleDivremOverflowImplEP12OverflowDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1114
  ret void, !dbg !1115
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL24handleDivremOverflowImplEP12OverflowDatamm(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1116 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  %7 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1117, !DIExpression(), !1118)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1119, !DIExpression(), !1120)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1121, !DIExpression(), !1122)
  %8 = load ptr, ptr %4, align 8, !dbg !1123
  %9 = getelementptr inbounds %struct.OverflowData, ptr %8, i32 0, i32 1, !dbg !1125
  %10 = load ptr, ptr %9, align 8, !dbg !1125
  %11 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %10), !dbg !1126
  br i1 %11, label %12, label %13, !dbg !1127

12:                                               ; preds = %3
  call void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef @.str.49.52, ptr noundef @.str.39) #8, !dbg !1128
  unreachable, !dbg !1128

13:                                               ; preds = %3
    #dbg_declare(ptr %7, !1129, !DIExpression(), !1131)
  store i32 13, ptr %7, align 4, !dbg !1131
  %14 = load i32, ptr %7, align 4, !dbg !1132
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %14) #8, !dbg !1133
  unreachable, !dbg !1133
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_divrem_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1134 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1135, !DIExpression(), !1136)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1137, !DIExpression(), !1138)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1139, !DIExpression(), !1140)
  %7 = load ptr, ptr %4, align 8, !dbg !1141
  %8 = load i64, ptr %5, align 8, !dbg !1142
  %9 = load i64, ptr %6, align 8, !dbg !1143
  call void @_ZN7__ubsanL24handleDivremOverflowImplEP12OverflowDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1144
  ret void, !dbg !1145
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_shift_out_of_bounds(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1146 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1151, !DIExpression(), !1152)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1153, !DIExpression(), !1154)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1155, !DIExpression(), !1156)
  %7 = load ptr, ptr %4, align 8, !dbg !1157
  %8 = load i64, ptr %5, align 8, !dbg !1158
  %9 = load i64, ptr %6, align 8, !dbg !1159
  call void @_ZN7__ubsanL26handleShiftOutOfBoundsImplEP20ShiftOutOfBoundsDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1160
  ret void, !dbg !1161
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL26handleShiftOutOfBoundsImplEP20ShiftOutOfBoundsDatamm(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1162 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1163, !DIExpression(), !1164)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1165, !DIExpression(), !1166)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1167, !DIExpression(), !1168)
  call void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef @.str.50, ptr noundef @.str.39) #8, !dbg !1169
  unreachable, !dbg !1169
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_shift_out_of_bounds_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1170 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1171, !DIExpression(), !1172)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1173, !DIExpression(), !1174)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1175, !DIExpression(), !1176)
  %7 = load ptr, ptr %4, align 8, !dbg !1177
  %8 = load i64, ptr %5, align 8, !dbg !1178
  %9 = load i64, ptr %6, align 8, !dbg !1179
  call void @_ZN7__ubsanL26handleShiftOutOfBoundsImplEP20ShiftOutOfBoundsDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1180
  ret void, !dbg !1181
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_out_of_bounds(ptr noundef %0, i64 noundef %1) #4 !dbg !1182 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1187, !DIExpression(), !1188)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1189, !DIExpression(), !1190)
  %5 = load ptr, ptr %3, align 8, !dbg !1191
  %6 = load i64, ptr %4, align 8, !dbg !1192
  call void @_ZN7__ubsanL21handleOutOfBoundsImplEP15OutOfBoundsDatam(ptr noundef %5, i64 noundef %6), !dbg !1193
  ret void, !dbg !1194
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL21handleOutOfBoundsImplEP15OutOfBoundsDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1195 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1196, !DIExpression(), !1197)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1198, !DIExpression(), !1199)
    #dbg_declare(ptr %5, !1200, !DIExpression(), !1201)
  store i32 22, ptr %5, align 4, !dbg !1201
  %6 = load i32, ptr %5, align 4, !dbg !1202
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %6) #8, !dbg !1203
  unreachable, !dbg !1203
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_out_of_bounds_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1204 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1205, !DIExpression(), !1206)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1207, !DIExpression(), !1208)
  %5 = load ptr, ptr %3, align 8, !dbg !1209
  %6 = load i64, ptr %4, align 8, !dbg !1210
  call void @_ZN7__ubsanL21handleOutOfBoundsImplEP15OutOfBoundsDatam(ptr noundef %5, i64 noundef %6), !dbg !1211
  ret void, !dbg !1212
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_builtin_unreachable(ptr noundef %0) #4 !dbg !1213 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1218, !DIExpression(), !1219)
  %3 = load ptr, ptr %2, align 8, !dbg !1220
  call void @_ZN7__ubsanL28handleBuiltinUnreachableImplEP15UnreachableData(ptr noundef %3), !dbg !1221
  ret void, !dbg !1222
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL28handleBuiltinUnreachableImplEP15UnreachableData(ptr noundef %0) #4 !dbg !1223 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1224, !DIExpression(), !1225)
    #dbg_declare(ptr %3, !1226, !DIExpression(), !1227)
  store i32 23, ptr %3, align 4, !dbg !1227
  %4 = load i32, ptr %3, align 4, !dbg !1228
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %4) #8, !dbg !1229
  unreachable, !dbg !1229
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_missing_return(ptr noundef %0) #4 !dbg !1230 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1231, !DIExpression(), !1232)
  %3 = load ptr, ptr %2, align 8, !dbg !1233
  call void @_ZN7__ubsanL23handleMissingReturnImplEP15UnreachableData(ptr noundef %3), !dbg !1234
  ret void, !dbg !1235
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL23handleMissingReturnImplEP15UnreachableData(ptr noundef %0) #4 !dbg !1236 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1237, !DIExpression(), !1238)
    #dbg_declare(ptr %3, !1239, !DIExpression(), !1240)
  store i32 24, ptr %3, align 4, !dbg !1240
  %4 = load i32, ptr %3, align 4, !dbg !1241
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %4) #8, !dbg !1242
  unreachable, !dbg !1242
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_vla_bound_not_positive(ptr noundef %0, i64 noundef %1) #4 !dbg !1243 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1248, !DIExpression(), !1249)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1250, !DIExpression(), !1251)
  %5 = load ptr, ptr %3, align 8, !dbg !1252
  %6 = load i64, ptr %4, align 8, !dbg !1253
  call void @_ZN7__ubsanL25handleVLABoundNotPositiveEP12VLABoundDatam(ptr noundef %5, i64 noundef %6), !dbg !1254
  ret void, !dbg !1255
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL25handleVLABoundNotPositiveEP12VLABoundDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1256 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1257, !DIExpression(), !1258)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1259, !DIExpression(), !1260)
    #dbg_declare(ptr %5, !1261, !DIExpression(), !1262)
  store i32 25, ptr %5, align 4, !dbg !1262
  %6 = load i32, ptr %5, align 4, !dbg !1263
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %6) #8, !dbg !1264
  unreachable, !dbg !1264
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_vla_bound_not_positive_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1265 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1266, !DIExpression(), !1267)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1268, !DIExpression(), !1269)
  %5 = load ptr, ptr %3, align 8, !dbg !1270
  %6 = load i64, ptr %4, align 8, !dbg !1271
  call void @_ZN7__ubsanL25handleVLABoundNotPositiveEP12VLABoundDatam(ptr noundef %5, i64 noundef %6), !dbg !1272
  ret void, !dbg !1273
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_float_cast_overflow(ptr noundef %0, i64 noundef %1) #4 !dbg !1274 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1278, !DIExpression(), !1279)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1280, !DIExpression(), !1281)
  %5 = load ptr, ptr %3, align 8, !dbg !1282
  %6 = load i64, ptr %4, align 8, !dbg !1283
  call void @_ZN7__ubsanL23handleFloatCastOverflowEPvm(ptr noundef %5, i64 noundef %6), !dbg !1284
  ret void, !dbg !1285
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL23handleFloatCastOverflowEPvm(ptr noundef %0, i64 noundef %1) #4 !dbg !1286 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1287, !DIExpression(), !1288)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1289, !DIExpression(), !1290)
    #dbg_declare(ptr %5, !1291, !DIExpression(), !1292)
  store i32 26, ptr %5, align 4, !dbg !1292
  %6 = load i32, ptr %5, align 4, !dbg !1293
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %6) #8, !dbg !1294
  unreachable, !dbg !1294
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_float_cast_overflow_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1295 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1296, !DIExpression(), !1297)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1298, !DIExpression(), !1299)
  %5 = load ptr, ptr %3, align 8, !dbg !1300
  %6 = load i64, ptr %4, align 8, !dbg !1301
  call void @_ZN7__ubsanL23handleFloatCastOverflowEPvm(ptr noundef %5, i64 noundef %6), !dbg !1302
  ret void, !dbg !1303
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_load_invalid_value(ptr noundef %0, i64 noundef %1) #4 !dbg !1304 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1309, !DIExpression(), !1310)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1311, !DIExpression(), !1312)
  %5 = load ptr, ptr %3, align 8, !dbg !1313
  %6 = load i64, ptr %4, align 8, !dbg !1314
  call void @_ZN7__ubsanL22handleLoadInvalidValueEP16InvalidValueDatam(ptr noundef %5, i64 noundef %6), !dbg !1315
  ret void, !dbg !1316
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL22handleLoadInvalidValueEP16InvalidValueDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1317 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1318, !DIExpression(), !1319)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1320, !DIExpression(), !1321)
  call void @_ZN7__ubsanL12report_errorEPKcS1_(ptr noundef @.str.51, ptr noundef @.str.46) #8, !dbg !1322
  unreachable, !dbg !1322
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_load_invalid_value_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1323 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1324, !DIExpression(), !1325)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1326, !DIExpression(), !1327)
  %5 = load ptr, ptr %3, align 8, !dbg !1328
  %6 = load i64, ptr %4, align 8, !dbg !1329
  call void @_ZN7__ubsanL22handleLoadInvalidValueEP16InvalidValueDatam(ptr noundef %5, i64 noundef %6), !dbg !1330
  ret void, !dbg !1331
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_implicit_conversion(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1332 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1342, !DIExpression(), !1343)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1344, !DIExpression(), !1345)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1346, !DIExpression(), !1347)
  %7 = load ptr, ptr %4, align 8, !dbg !1348
  %8 = load i64, ptr %5, align 8, !dbg !1349
  %9 = load i64, ptr %6, align 8, !dbg !1350
  call void @_ZN7__ubsanL24handleImplicitConversionEP22ImplicitConversionDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1351
  ret void, !dbg !1352
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL24handleImplicitConversionEP22ImplicitConversionDatamm(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1353 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  %7 = alloca i32, align 4
  %8 = alloca ptr, align 8
  %9 = alloca ptr, align 8
  %10 = alloca i8, align 1
  %11 = alloca i8, align 1
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1354, !DIExpression(), !1355)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1356, !DIExpression(), !1357)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1358, !DIExpression(), !1359)
    #dbg_declare(ptr %7, !1360, !DIExpression(), !1361)
  store i32 0, ptr %7, align 4, !dbg !1361
    #dbg_declare(ptr %8, !1362, !DIExpression(), !1363)
  %12 = load ptr, ptr %4, align 8, !dbg !1364
  %13 = getelementptr inbounds %struct.ImplicitConversionData, ptr %12, i32 0, i32 1, !dbg !1365
  %14 = load ptr, ptr %13, align 8, !dbg !1365
  store ptr %14, ptr %8, align 8, !dbg !1363
    #dbg_declare(ptr %9, !1366, !DIExpression(), !1367)
  %15 = load ptr, ptr %4, align 8, !dbg !1368
  %16 = getelementptr inbounds %struct.ImplicitConversionData, ptr %15, i32 0, i32 2, !dbg !1369
  %17 = load ptr, ptr %16, align 8, !dbg !1369
  store ptr %17, ptr %9, align 8, !dbg !1367
    #dbg_declare(ptr %10, !1370, !DIExpression(), !1371)
  %18 = load ptr, ptr %8, align 8, !dbg !1372
  %19 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %18), !dbg !1373
  %20 = zext i1 %19 to i8, !dbg !1371
  store i8 %20, ptr %10, align 1, !dbg !1371
    #dbg_declare(ptr %11, !1374, !DIExpression(), !1375)
  %21 = load ptr, ptr %9, align 8, !dbg !1376
  %22 = call noundef zeroext i1 @_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv(ptr noundef nonnull align 2 dereferenceable(5) %21), !dbg !1377
  %23 = zext i1 %22 to i8, !dbg !1375
  store i8 %23, ptr %11, align 1, !dbg !1375
  %24 = load ptr, ptr %4, align 8, !dbg !1378
  %25 = getelementptr inbounds %struct.ImplicitConversionData, ptr %24, i32 0, i32 3, !dbg !1379
  %26 = load i8, ptr %25, align 8, !dbg !1379
  %27 = zext i8 %26 to i32, !dbg !1378
  switch i32 %27, label %40 [
    i32 0, label %28
    i32 1, label %36
    i32 2, label %37
    i32 3, label %38
    i32 4, label %39
  ], !dbg !1380

28:                                               ; preds = %3
  %29 = load i8, ptr %10, align 1, !dbg !1381
  %30 = trunc i8 %29 to i1, !dbg !1381
  br i1 %30, label %35, label %31, !dbg !1385

31:                                               ; preds = %28
  %32 = load i8, ptr %11, align 1, !dbg !1386
  %33 = trunc i8 %32 to i1, !dbg !1386
  br i1 %33, label %35, label %34, !dbg !1387

34:                                               ; preds = %31
  store i32 16, ptr %7, align 4, !dbg !1388
  br label %40, !dbg !1390

35:                                               ; preds = %31, %28
  store i32 17, ptr %7, align 4, !dbg !1391
  br label %40

36:                                               ; preds = %3
  store i32 16, ptr %7, align 4, !dbg !1393
  br label %40, !dbg !1394

37:                                               ; preds = %3
  store i32 17, ptr %7, align 4, !dbg !1395
  br label %40, !dbg !1396

38:                                               ; preds = %3
  store i32 18, ptr %7, align 4, !dbg !1397
  br label %40, !dbg !1398

39:                                               ; preds = %3
  store i32 19, ptr %7, align 4, !dbg !1399
  br label %40, !dbg !1400

40:                                               ; preds = %34, %35, %3, %39, %38, %37, %36
  %41 = load i32, ptr %7, align 4, !dbg !1401
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %41) #8, !dbg !1402
  unreachable, !dbg !1402
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_implicit_conversion_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1403 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1404, !DIExpression(), !1405)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1406, !DIExpression(), !1407)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1408, !DIExpression(), !1409)
  %7 = load ptr, ptr %4, align 8, !dbg !1410
  %8 = load i64, ptr %5, align 8, !dbg !1411
  %9 = load i64, ptr %6, align 8, !dbg !1412
  call void @_ZN7__ubsanL24handleImplicitConversionEP22ImplicitConversionDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1413
  ret void, !dbg !1414
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_invalid_builtin(ptr noundef %0) #4 !dbg !1415 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1420, !DIExpression(), !1421)
  %3 = load ptr, ptr %2, align 8, !dbg !1422
  call void @_ZN7__ubsanL20handleInvalidBuiltinEP18InvalidBuiltinData(ptr noundef %3), !dbg !1423
  ret void, !dbg !1424
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL20handleInvalidBuiltinEP18InvalidBuiltinData(ptr noundef %0) #4 !dbg !1425 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1426, !DIExpression(), !1427)
    #dbg_declare(ptr %3, !1428, !DIExpression(), !1429)
  store i32 14, ptr %3, align 4, !dbg !1429
  %4 = load i32, ptr %3, align 4, !dbg !1430
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %4) #8, !dbg !1431
  unreachable, !dbg !1431
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_invalid_builtin_abort(ptr noundef %0) #4 !dbg !1432 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1433, !DIExpression(), !1434)
  %3 = load ptr, ptr %2, align 8, !dbg !1435
  call void @_ZN7__ubsanL20handleInvalidBuiltinEP18InvalidBuiltinData(ptr noundef %3), !dbg !1436
  ret void, !dbg !1437
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nonnull_return_v1(ptr noundef %0, ptr noundef %1) #4 !dbg !1438 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1444, !DIExpression(), !1445)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1446, !DIExpression(), !1447)
  %5 = load ptr, ptr %3, align 8, !dbg !1448
  %6 = load ptr, ptr %4, align 8, !dbg !1449
  call void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %5, ptr noundef %6, i1 noundef zeroext true), !dbg !1450
  ret void, !dbg !1451
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %0, ptr noundef %1, i1 noundef zeroext %2) #4 !dbg !1452 {
  %4 = alloca ptr, align 8
  %5 = alloca ptr, align 8
  %6 = alloca i8, align 1
  %7 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1455, !DIExpression(), !1456)
  store ptr %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1457, !DIExpression(), !1458)
  %8 = zext i1 %2 to i8
  store i8 %8, ptr %6, align 1
    #dbg_declare(ptr %6, !1459, !DIExpression(), !1460)
    #dbg_declare(ptr %7, !1461, !DIExpression(), !1462)
  %9 = load i8, ptr %6, align 1, !dbg !1463
  %10 = trunc i8 %9 to i1, !dbg !1463
  %11 = zext i1 %10 to i64, !dbg !1463
  %12 = select i1 %10, i32 30, i32 31, !dbg !1463
  store i32 %12, ptr %7, align 4, !dbg !1462
  %13 = load i32, ptr %7, align 4, !dbg !1464
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %13) #8, !dbg !1465
  unreachable, !dbg !1465
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nonnull_return_v1_abort(ptr noundef %0, ptr noundef %1) #4 !dbg !1466 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1467, !DIExpression(), !1468)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1469, !DIExpression(), !1470)
  %5 = load ptr, ptr %3, align 8, !dbg !1471
  %6 = load ptr, ptr %4, align 8, !dbg !1472
  call void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %5, ptr noundef %6, i1 noundef zeroext true), !dbg !1473
  ret void, !dbg !1474
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nullability_return_v1(ptr noundef %0, ptr noundef %1) #4 !dbg !1475 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1476, !DIExpression(), !1477)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1478, !DIExpression(), !1479)
  %5 = load ptr, ptr %3, align 8, !dbg !1480
  %6 = load ptr, ptr %4, align 8, !dbg !1481
  call void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %5, ptr noundef %6, i1 noundef zeroext false), !dbg !1482
  ret void, !dbg !1483
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nullability_return_v1_abort(ptr noundef %0, ptr noundef %1) #4 !dbg !1484 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1485, !DIExpression(), !1486)
  store ptr %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1487, !DIExpression(), !1488)
  %5 = load ptr, ptr %3, align 8, !dbg !1489
  %6 = load ptr, ptr %4, align 8, !dbg !1490
  call void @_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb(ptr noundef %5, ptr noundef %6, i1 noundef zeroext false), !dbg !1491
  ret void, !dbg !1492
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nonnull_arg(ptr noundef %0) #4 !dbg !1493 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1498, !DIExpression(), !1499)
  %3 = load ptr, ptr %2, align 8, !dbg !1500
  call void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %3, i1 noundef zeroext true), !dbg !1501
  ret void, !dbg !1502
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %0, i1 noundef zeroext %1) #4 !dbg !1503 {
  %3 = alloca ptr, align 8
  %4 = alloca i8, align 1
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1506, !DIExpression(), !1507)
  %6 = zext i1 %1 to i8
  store i8 %6, ptr %4, align 1
    #dbg_declare(ptr %4, !1508, !DIExpression(), !1509)
    #dbg_declare(ptr %5, !1510, !DIExpression(), !1511)
  %7 = load i8, ptr %4, align 1, !dbg !1512
  %8 = trunc i8 %7 to i1, !dbg !1512
  %9 = zext i1 %8 to i64, !dbg !1512
  %10 = select i1 %8, i32 32, i32 33, !dbg !1512
  store i32 %10, ptr %5, align 4, !dbg !1511
  %11 = load i32, ptr %5, align 4, !dbg !1513
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %11) #8, !dbg !1514
  unreachable, !dbg !1514
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nonnull_arg_abort(ptr noundef %0) #4 !dbg !1515 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1516, !DIExpression(), !1517)
  %3 = load ptr, ptr %2, align 8, !dbg !1518
  call void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %3, i1 noundef zeroext true), !dbg !1519
  ret void, !dbg !1520
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nullability_arg(ptr noundef %0) #4 !dbg !1521 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1522, !DIExpression(), !1523)
  %3 = load ptr, ptr %2, align 8, !dbg !1524
  call void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %3, i1 noundef zeroext false), !dbg !1525
  ret void, !dbg !1526
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_nullability_arg_abort(ptr noundef %0) #4 !dbg !1527 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
    #dbg_declare(ptr %2, !1528, !DIExpression(), !1529)
  %3 = load ptr, ptr %2, align 8, !dbg !1530
  call void @_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab(ptr noundef %3, i1 noundef zeroext false), !dbg !1531
  ret void, !dbg !1532
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_pointer_overflow(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1533 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1538, !DIExpression(), !1539)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1540, !DIExpression(), !1541)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1542, !DIExpression(), !1543)
  %7 = load ptr, ptr %4, align 8, !dbg !1544
  %8 = load i64, ptr %5, align 8, !dbg !1545
  %9 = load i64, ptr %6, align 8, !dbg !1546
  call void @_ZN7__ubsanL25handlePointerOverflowImplEP19PointerOverflowDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1547
  ret void, !dbg !1548
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL25handlePointerOverflowImplEP19PointerOverflowDatamm(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1549 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  %7 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1550, !DIExpression(), !1551)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1552, !DIExpression(), !1553)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1554, !DIExpression(), !1555)
    #dbg_declare(ptr %7, !1556, !DIExpression(), !1557)
  %8 = load i64, ptr %5, align 8, !dbg !1558
  %9 = icmp eq i64 %8, 0, !dbg !1560
  %10 = load i64, ptr %6, align 8
  %11 = icmp eq i64 %10, 0
  %or.cond = select i1 %9, i1 %11, i1 false, !dbg !1561
  br i1 %or.cond, label %12, label %13, !dbg !1561

12:                                               ; preds = %3
  store i32 3, ptr %7, align 4, !dbg !1562
  br label %26, !dbg !1563

13:                                               ; preds = %3
  %14 = load i64, ptr %5, align 8, !dbg !1564
  %15 = icmp eq i64 %14, 0, !dbg !1566
  %16 = load i64, ptr %6, align 8
  %17 = icmp ne i64 %16, 0
  %or.cond3 = select i1 %15, i1 %17, i1 false, !dbg !1567
  br i1 %or.cond3, label %18, label %19, !dbg !1567

18:                                               ; preds = %13
  store i32 4, ptr %7, align 4, !dbg !1568
  br label %26, !dbg !1569

19:                                               ; preds = %13
  %20 = load i64, ptr %5, align 8, !dbg !1570
  %21 = icmp ne i64 %20, 0, !dbg !1572
  %22 = load i64, ptr %6, align 8
  %23 = icmp eq i64 %22, 0
  %or.cond5 = select i1 %21, i1 %23, i1 false, !dbg !1573
  br i1 %or.cond5, label %24, label %25, !dbg !1573

24:                                               ; preds = %19
  store i32 5, ptr %7, align 4, !dbg !1574
  br label %26, !dbg !1575

25:                                               ; preds = %19
  store i32 6, ptr %7, align 4, !dbg !1576
  br label %26

26:                                               ; preds = %18, %25, %24, %12
  %27 = load i32, ptr %7, align 4, !dbg !1577
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %27) #8, !dbg !1578
  unreachable, !dbg !1578
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_pointer_overflow_abort(ptr noundef %0, i64 noundef %1, i64 noundef %2) #4 !dbg !1579 {
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !1580, !DIExpression(), !1581)
  store i64 %1, ptr %5, align 8
    #dbg_declare(ptr %5, !1582, !DIExpression(), !1583)
  store i64 %2, ptr %6, align 8
    #dbg_declare(ptr %6, !1584, !DIExpression(), !1585)
  %7 = load ptr, ptr %4, align 8, !dbg !1586
  %8 = load i64, ptr %5, align 8, !dbg !1587
  %9 = load i64, ptr %6, align 8, !dbg !1588
  call void @_ZN7__ubsanL25handlePointerOverflowImplEP19PointerOverflowDatamm(ptr noundef %7, i64 noundef %8, i64 noundef %9), !dbg !1589
  ret void, !dbg !1590
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_function_type_mismatch(ptr noundef %0, i64 noundef %1) #4 !dbg !1591 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1596, !DIExpression(), !1597)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1598, !DIExpression(), !1599)
  %5 = load ptr, ptr %3, align 8, !dbg !1600
  %6 = load i64, ptr %4, align 8, !dbg !1601
  call void @_ZN7__ubsanL26handleFunctionTypeMismatchEP24FunctionTypeMismatchDatam(ptr noundef %5, i64 noundef %6), !dbg !1602
  ret void, !dbg !1603
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define internal void @_ZN7__ubsanL26handleFunctionTypeMismatchEP24FunctionTypeMismatchDatam(ptr noundef %0, i64 noundef %1) #4 !dbg !1604 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1605, !DIExpression(), !1606)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1607, !DIExpression(), !1608)
    #dbg_declare(ptr %5, !1609, !DIExpression(), !1610)
  store i32 29, ptr %5, align 4, !dbg !1610
  %6 = load i32, ptr %5, align 4, !dbg !1611
  call void @_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE(i32 noundef %6) #8, !dbg !1612
  unreachable, !dbg !1612
}

; Function Attrs: mustprogress noinline sspstrong uwtable
define void @__ubsan_handle_function_type_mismatch_abort(ptr noundef %0, i64 noundef %1) #4 !dbg !1613 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1614, !DIExpression(), !1615)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1616, !DIExpression(), !1617)
  %5 = load ptr, ptr %3, align 8, !dbg !1618
  %6 = load i64, ptr %4, align 8, !dbg !1619
  call void @_ZN7__ubsanL26handleFunctionTypeMismatchEP24FunctionTypeMismatchDatam(ptr noundef %5, i64 noundef %6), !dbg !1620
  ret void, !dbg !1621
}

; Function Attrs: noreturn nounwind
declare void @abort() #7

; Function Attrs: noinline nounwind sspstrong uwtable
define void @klee_overshift_check(i64 noundef %0, i64 noundef %1) #0 !dbg !1622 {
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  store i64 %0, ptr %3, align 8
    #dbg_declare(ptr %3, !1626, !DIExpression(), !1627)
  store i64 %1, ptr %4, align 8
    #dbg_declare(ptr %4, !1628, !DIExpression(), !1629)
  %5 = load i64, ptr %4, align 8, !dbg !1630
  %6 = load i64, ptr %3, align 8, !dbg !1632
  %7 = icmp uge i64 %5, %6, !dbg !1633
  br i1 %7, label %8, label %9, !dbg !1634

8:                                                ; preds = %2
  call void @klee_report_error(ptr noundef @.str.57, i32 noundef 0, ptr noundef @.str.1.58, ptr noundef @.str.2.59) #8, !dbg !1635
  unreachable, !dbg !1635

9:                                                ; preds = %2
  ret void, !dbg !1637
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
!641 = !DICompositeType(tag: DW_TAG_array_type, baseType: !251, size: 4192, elements: !642)
!642 = !{!643}
!643 = !DISubrange(count: 131)
!644 = !DILocation(line: 19, column: 14, scope: !637)
!645 = !DILocalVariable(name: "data", scope: !637, file: !2, line: 20, type: !646)
!646 = !DICompositeType(tag: DW_TAG_array_type, baseType: !251, size: 2048, elements: !647)
!647 = !{!648}
!648 = !DISubrange(count: 64)
!649 = !DILocation(line: 20, column: 14, scope: !637)
!650 = !DILocalVariable(name: "permutation", scope: !637, file: !2, line: 20, type: !646)
!651 = !DILocation(line: 20, column: 30, scope: !637)
!652 = !DILocalVariable(name: "target", scope: !637, file: !2, line: 21, type: !646)
!653 = !DILocation(line: 21, column: 14, scope: !637)
!654 = !DILocalVariable(name: "used", scope: !637, file: !2, line: 21, type: !646)
!655 = !DILocation(line: 21, column: 32, scope: !637)
!656 = !DILocalVariable(name: "trace", scope: !637, file: !2, line: 21, type: !657)
!657 = !DICompositeType(tag: DW_TAG_array_type, baseType: !251, size: 4096, elements: !658)
!658 = !{!659}
!659 = !DISubrange(count: 128)
!660 = !DILocation(line: 21, column: 48, scope: !637)
!661 = !DILocalVariable(name: "out", scope: !637, file: !2, line: 21, type: !662)
!662 = !DICompositeType(tag: DW_TAG_array_type, baseType: !251, size: 96, elements: !663)
!663 = !{!664}
!664 = !DISubrange(count: 3)
!665 = !DILocation(line: 21, column: 70, scope: !637)
!666 = !DILocation(line: 22, column: 24, scope: !637)
!667 = !DILocation(line: 22, column: 5, scope: !637)
!668 = !DILocalVariable(name: "valid", scope: !637, file: !2, line: 23, type: !251)
!669 = !DILocation(line: 23, column: 14, scope: !637)
!670 = !DILocalVariable(name: "i", scope: !671, file: !2, line: 24, type: !251)
!671 = distinct !DILexicalBlock(scope: !637, file: !2, line: 24, column: 5)
!672 = !DILocation(line: 24, column: 19, scope: !671)
!673 = !DILocation(line: 24, column: 10, scope: !671)
!674 = !DILocation(line: 24, column: 26, scope: !675)
!675 = distinct !DILexicalBlock(scope: !671, file: !2, line: 24, column: 5)
!676 = !DILocation(line: 24, column: 28, scope: !675)
!677 = !DILocation(line: 24, column: 5, scope: !671)
!678 = !DILocation(line: 25, column: 24, scope: !679)
!679 = distinct !DILexicalBlock(scope: !675, file: !2, line: 24, column: 45)
!680 = !DILocation(line: 25, column: 18, scope: !679)
!681 = !{!"branch_weights", i32 1048575, i32 1}
!682 = !DILocation(line: 25, column: 27, scope: !679)
!683 = !DILocation(line: 25, column: 15, scope: !679)
!684 = !DILocalVariable(name: "j", scope: !685, file: !2, line: 26, type: !251)
!685 = distinct !DILexicalBlock(scope: !679, file: !2, line: 26, column: 9)
!686 = !DILocation(line: 26, column: 23, scope: !685)
!687 = !DILocation(line: 26, column: 14, scope: !685)
!688 = !DILocation(line: 26, column: 30, scope: !689)
!689 = distinct !DILexicalBlock(scope: !685, file: !2, line: 26, column: 9)
!690 = !DILocation(line: 26, column: 34, scope: !689)
!691 = !DILocation(line: 26, column: 32, scope: !689)
!692 = !DILocation(line: 26, column: 9, scope: !685)
!693 = !DILocation(line: 27, column: 28, scope: !689)
!694 = !DILocation(line: 27, column: 22, scope: !689)
!695 = !DILocation(line: 27, column: 40, scope: !689)
!696 = !DILocation(line: 27, column: 34, scope: !689)
!697 = !DILocation(line: 27, column: 31, scope: !689)
!698 = !DILocation(line: 27, column: 19, scope: !689)
!699 = !DILocation(line: 26, column: 37, scope: !689)
!700 = !DILocation(line: 26, column: 9, scope: !689)
!701 = distinct !{!701, !692, !702, !703}
!702 = !DILocation(line: 27, column: 41, scope: !685)
!703 = !{!"llvm.loop.mustprogress"}
!704 = !DILocation(line: 28, column: 32, scope: !679)
!705 = !DILocation(line: 28, column: 26, scope: !679)
!706 = !DILocation(line: 28, column: 21, scope: !679)
!707 = !DILocation(line: 28, column: 24, scope: !679)
!708 = !DILocation(line: 29, column: 36, scope: !679)
!709 = !DILocation(line: 29, column: 34, scope: !679)
!710 = !DILocation(line: 29, column: 19, scope: !679)
!711 = !DILocation(line: 29, column: 14, scope: !679)
!712 = !DILocation(line: 29, column: 17, scope: !679)
!713 = !DILocation(line: 24, column: 40, scope: !675)
!714 = !DILocation(line: 24, column: 5, scope: !675)
!715 = distinct !{!715, !677, !716, !703}
!716 = !DILocation(line: 30, column: 5, scope: !671)
!717 = !DILocation(line: 33, column: 17, scope: !637)
!718 = !DILocation(line: 33, column: 23, scope: !637)
!719 = !DILocation(line: 33, column: 5, scope: !637)
!720 = !DILocalVariable(name: "i", scope: !721, file: !2, line: 34, type: !251)
!721 = distinct !DILexicalBlock(scope: !637, file: !2, line: 34, column: 5)
!722 = !DILocation(line: 34, column: 19, scope: !721)
!723 = !DILocation(line: 34, column: 10, scope: !721)
!724 = !DILocation(line: 34, column: 26, scope: !725)
!725 = distinct !DILexicalBlock(scope: !721, file: !2, line: 34, column: 5)
!726 = !DILocation(line: 34, column: 28, scope: !725)
!727 = !DILocation(line: 34, column: 5, scope: !721)
!728 = !DILocation(line: 35, column: 40, scope: !725)
!729 = !DILocation(line: 35, column: 38, scope: !725)
!730 = !DILocation(line: 35, column: 18, scope: !725)
!731 = !DILocation(line: 35, column: 13, scope: !725)
!732 = !DILocation(line: 35, column: 16, scope: !725)
!733 = !DILocation(line: 34, column: 34, scope: !725)
!734 = !DILocation(line: 34, column: 5, scope: !725)
!735 = distinct !{!735, !727, !736, !703}
!736 = !DILocation(line: 35, column: 41, scope: !721)
!737 = !DILocalVariable(name: "status", scope: !637, file: !2, line: 36, type: !251)
!738 = !DILocation(line: 36, column: 14, scope: !637)
!739 = !DILocation(line: 36, column: 41, scope: !637)
!740 = !DILocation(line: 36, column: 47, scope: !637)
!741 = !DILocation(line: 36, column: 60, scope: !637)
!742 = !DILocation(line: 36, column: 68, scope: !637)
!743 = !DILocation(line: 36, column: 74, scope: !637)
!744 = !DILocation(line: 36, column: 81, scope: !637)
!745 = !DILocation(line: 36, column: 23, scope: !637)
!746 = !DILocation(line: 37, column: 5, scope: !637)
!747 = !DILocalVariable(name: "i", scope: !748, file: !2, line: 38, type: !251)
!748 = distinct !DILexicalBlock(scope: !637, file: !2, line: 38, column: 5)
!749 = !DILocation(line: 38, column: 19, scope: !748)
!750 = !DILocation(line: 38, column: 10, scope: !748)
!751 = !DILocation(line: 38, column: 26, scope: !752)
!752 = distinct !DILexicalBlock(scope: !748, file: !2, line: 38, column: 5)
!753 = !DILocation(line: 38, column: 28, scope: !752)
!754 = !DILocation(line: 38, column: 5, scope: !748)
!755 = !DILocation(line: 39, column: 9, scope: !756)
!756 = distinct !DILexicalBlock(scope: !752, file: !2, line: 38, column: 45)
!757 = !DILocation(line: 40, column: 9, scope: !756)
!758 = !DILocation(line: 38, column: 40, scope: !752)
!759 = !DILocation(line: 38, column: 5, scope: !752)
!760 = distinct !{!760, !754, !761, !703}
!761 = !DILocation(line: 41, column: 5, scope: !748)
!762 = !DILocalVariable(name: "i", scope: !763, file: !2, line: 43, type: !251)
!763 = distinct !DILexicalBlock(scope: !637, file: !2, line: 43, column: 5)
!764 = !DILocation(line: 43, column: 19, scope: !763)
!765 = !DILocation(line: 43, column: 10, scope: !763)
!766 = !DILocation(line: 43, column: 26, scope: !767)
!767 = distinct !DILexicalBlock(scope: !763, file: !2, line: 43, column: 5)
!768 = !DILocation(line: 43, column: 28, scope: !767)
!769 = !DILocation(line: 43, column: 5, scope: !763)
!770 = !DILocation(line: 44, column: 9, scope: !767)
!771 = !DILocation(line: 43, column: 34, scope: !767)
!772 = !DILocation(line: 43, column: 5, scope: !767)
!773 = distinct !{!773, !769, !774, !703}
!774 = !DILocation(line: 44, column: 9, scope: !763)
!775 = !DILocation(line: 45, column: 5, scope: !637)
!776 = distinct !DISubprogram(name: "main", scope: !32, file: !32, line: 6, type: !638, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !215, retainedNodes: !334)
!777 = !DILocalVariable(name: "result", scope: !776, file: !32, line: 8, type: !258)
!778 = !DILocation(line: 8, column: 9, scope: !776)
!779 = !DILocation(line: 8, column: 18, scope: !776)
!780 = !DILocalVariable(name: "completed", scope: !776, file: !32, line: 9, type: !781)
!781 = !DIBasicType(name: "unsigned char", size: 8, encoding: DW_ATE_unsigned_char)
!782 = !DILocation(line: 9, column: 19, scope: !776)
!783 = !DILocation(line: 11, column: 5, scope: !776)
!784 = !DILocation(line: 12, column: 12, scope: !776)
!785 = !DILocation(line: 12, column: 5, scope: !776)
!786 = distinct !DISubprogram(name: "__ubsan_handle_type_mismatch_v1", scope: !38, file: !38, line: 174, type: !787, scopeLine: 175, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!787 = !DISubroutineType(types: !788)
!788 = !{null, !789, !798}
!789 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !790, size: 64)
!790 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "TypeMismatchData", file: !317, line: 25, size: 256, flags: DIFlagTypePassByValue | DIFlagNonTrivial, elements: !791, identifier: "_ZTS16TypeMismatchData")
!791 = !{!792, !794, !796, !797}
!792 = !DIDerivedType(tag: DW_TAG_member, name: "Loc", scope: !790, file: !317, line: 26, baseType: !793, size: 128)
!793 = !DICompositeType(tag: DW_TAG_class_type, name: "SourceLocation", scope: !224, file: !222, line: 28, size: 128, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTSN7__ubsan14SourceLocationE")
!794 = !DIDerivedType(tag: DW_TAG_member, name: "Type", scope: !790, file: !317, line: 27, baseType: !795, size: 64, offset: 128)
!795 = !DIDerivedType(tag: DW_TAG_reference_type, baseType: !241, size: 64)
!796 = !DIDerivedType(tag: DW_TAG_member, name: "LogAlignment", scope: !790, file: !317, line: 28, baseType: !781, size: 8, offset: 192)
!797 = !DIDerivedType(tag: DW_TAG_member, name: "TypeCheckKind", scope: !790, file: !317, line: 29, baseType: !781, size: 8, offset: 200)
!798 = !DIDerivedType(tag: DW_TAG_typedef, name: "ValueHandle", scope: !224, file: !222, line: 78, baseType: !311)
!799 = !DILocalVariable(name: "Data", arg: 1, scope: !786, file: !38, line: 174, type: !789)
!800 = !DILocation(line: 174, column: 67, scope: !786)
!801 = !DILocalVariable(name: "Pointer", arg: 2, scope: !786, file: !38, line: 175, type: !798)
!802 = !DILocation(line: 175, column: 61, scope: !786)
!803 = !DILocation(line: 177, column: 26, scope: !786)
!804 = !DILocation(line: 177, column: 32, scope: !786)
!805 = !DILocation(line: 177, column: 3, scope: !786)
!806 = !DILocation(line: 178, column: 1, scope: !786)
!807 = distinct !DISubprogram(name: "handleTypeMismatchImpl", linkageName: "_ZN7__ubsanL22handleTypeMismatchImplEP16TypeMismatchDatam", scope: !224, file: !38, line: 158, type: !787, scopeLine: 159, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!808 = !DILocalVariable(name: "Data", arg: 1, scope: !807, file: !38, line: 158, type: !789)
!809 = !DILocation(line: 158, column: 54, scope: !807)
!810 = !DILocalVariable(name: "Pointer", arg: 2, scope: !807, file: !38, line: 159, type: !798)
!811 = !DILocation(line: 159, column: 48, scope: !807)
!812 = !DILocalVariable(name: "Alignment", scope: !807, file: !38, line: 160, type: !311)
!813 = !DILocation(line: 160, column: 8, scope: !807)
!814 = !DILocation(line: 160, column: 31, scope: !807)
!815 = !DILocation(line: 160, column: 37, scope: !807)
!816 = !DILocation(line: 160, column: 28, scope: !807)
!817 = !{!"True"}
!818 = !DILocalVariable(name: "ET", scope: !807, file: !38, line: 161, type: !256)
!819 = !DILocation(line: 161, column: 13, scope: !807)
!820 = !DILocation(line: 162, column: 8, scope: !821)
!821 = distinct !DILexicalBlock(scope: !807, file: !38, line: 162, column: 7)
!822 = !DILocation(line: 162, column: 7, scope: !807)
!823 = !DILocation(line: 163, column: 11, scope: !821)
!824 = !DILocation(line: 163, column: 17, scope: !821)
!825 = !DILocation(line: 163, column: 31, scope: !821)
!826 = !DILocation(line: 163, column: 10, scope: !821)
!827 = !DILocation(line: 163, column: 8, scope: !821)
!828 = !DILocation(line: 163, column: 5, scope: !821)
!829 = !DILocation(line: 166, column: 12, scope: !830)
!830 = distinct !DILexicalBlock(scope: !821, file: !38, line: 166, column: 12)
!831 = !DILocation(line: 166, column: 23, scope: !830)
!832 = !DILocation(line: 166, column: 33, scope: !830)
!833 = !DILocation(line: 166, column: 20, scope: !830)
!834 = !DILocation(line: 166, column: 12, scope: !821)
!835 = !DILocation(line: 167, column: 8, scope: !830)
!836 = !DILocation(line: 167, column: 5, scope: !830)
!837 = !DILocation(line: 169, column: 8, scope: !830)
!838 = !DILocation(line: 171, column: 21, scope: !807)
!839 = !DILocation(line: 171, column: 3, scope: !807)
!840 = distinct !DISubprogram(name: "report_error_type", linkageName: "_ZN7__ubsanL17report_error_typeENS_9ErrorTypeE", scope: !224, file: !38, line: 115, type: !841, scopeLine: 115, flags: DIFlagPrototyped | DIFlagNoReturn, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!841 = !DISubroutineType(types: !842)
!842 = !{null, !256}
!843 = !DILocalVariable(name: "ET", arg: 1, scope: !840, file: !38, line: 115, type: !256)
!844 = !DILocation(line: 115, column: 67, scope: !840)
!845 = !DILocation(line: 116, column: 36, scope: !840)
!846 = !DILocation(line: 116, column: 16, scope: !840)
!847 = !DILocation(line: 116, column: 52, scope: !840)
!848 = !DILocation(line: 116, column: 41, scope: !840)
!849 = !DILocation(line: 116, column: 3, scope: !840)
!850 = distinct !DISubprogram(name: "ConvertTypeToString", linkageName: "_ZN7__ubsanL19ConvertTypeToStringENS_9ErrorTypeE", scope: !224, file: !38, line: 25, type: !851, scopeLine: 25, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!851 = !DISubroutineType(types: !852)
!852 = !{!239, !256}
!853 = !DILocalVariable(name: "Type", arg: 1, scope: !850, file: !38, line: 25, type: !256)
!854 = !DILocation(line: 25, column: 50, scope: !850)
!855 = !DILocation(line: 26, column: 11, scope: !850)
!856 = !DILocation(line: 26, column: 3, scope: !850)
!857 = !DILocation(line: 27, column: 1, scope: !858)
!858 = !DILexicalBlockFile(scope: !859, file: !53, discriminator: 0)
!859 = distinct !DILexicalBlock(scope: !850, file: !38, line: 26, column: 17)
!860 = !DILocation(line: 28, column: 1, scope: !858)
!861 = !DILocation(line: 29, column: 1, scope: !858)
!862 = !DILocation(line: 31, column: 1, scope: !858)
!863 = !DILocation(line: 32, column: 1, scope: !858)
!864 = !DILocation(line: 34, column: 1, scope: !858)
!865 = !DILocation(line: 36, column: 1, scope: !858)
!866 = !DILocation(line: 37, column: 1, scope: !858)
!867 = !DILocation(line: 38, column: 1, scope: !858)
!868 = !DILocation(line: 39, column: 1, scope: !858)
!869 = !DILocation(line: 40, column: 1, scope: !858)
!870 = !DILocation(line: 42, column: 1, scope: !858)
!871 = !DILocation(line: 44, column: 1, scope: !858)
!872 = !DILocation(line: 46, column: 1, scope: !858)
!873 = !DILocation(line: 47, column: 1, scope: !858)
!874 = !DILocation(line: 48, column: 1, scope: !858)
!875 = !DILocation(line: 49, column: 1, scope: !858)
!876 = !DILocation(line: 52, column: 1, scope: !858)
!877 = !DILocation(line: 55, column: 1, scope: !858)
!878 = !DILocation(line: 58, column: 1, scope: !858)
!879 = !DILocation(line: 61, column: 1, scope: !858)
!880 = !DILocation(line: 62, column: 1, scope: !858)
!881 = !DILocation(line: 63, column: 1, scope: !858)
!882 = !DILocation(line: 64, column: 1, scope: !858)
!883 = !DILocation(line: 65, column: 1, scope: !858)
!884 = !DILocation(line: 66, column: 1, scope: !858)
!885 = !DILocation(line: 67, column: 1, scope: !858)
!886 = !DILocation(line: 68, column: 1, scope: !858)
!887 = !DILocation(line: 69, column: 1, scope: !858)
!888 = !DILocation(line: 70, column: 1, scope: !858)
!889 = !DILocation(line: 71, column: 1, scope: !858)
!890 = !DILocation(line: 73, column: 1, scope: !858)
!891 = !DILocation(line: 75, column: 1, scope: !858)
!892 = !DILocation(line: 76, column: 1, scope: !858)
!893 = !DILocation(line: 78, column: 1, scope: !858)
!894 = !DILocation(line: 79, column: 1, scope: !858)
!895 = !DILocation(line: 32, column: 3, scope: !896)
!896 = !DILexicalBlockFile(scope: !859, file: !38, discriminator: 0)
!897 = !DILocation(line: 33, column: 1, scope: !850)
!898 = distinct !DISubprogram(name: "get_suffix", linkageName: "_ZN7__ubsanL10get_suffixENS_9ErrorTypeE", scope: !224, file: !38, line: 40, type: !851, scopeLine: 40, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!899 = !DILocalVariable(name: "ET", arg: 1, scope: !898, file: !38, line: 40, type: !256)
!900 = !DILocation(line: 40, column: 41, scope: !898)
!901 = !DILocation(line: 41, column: 11, scope: !898)
!902 = !DILocation(line: 41, column: 3, scope: !898)
!903 = !DILocation(line: 46, column: 5, scope: !904)
!904 = distinct !DILexicalBlock(scope: !898, file: !38, line: 41, column: 15)
!905 = !DILocation(line: 55, column: 5, scope: !904)
!906 = !DILocation(line: 59, column: 5, scope: !904)
!907 = !DILocation(line: 62, column: 5, scope: !904)
!908 = !DILocation(line: 65, column: 5, scope: !904)
!909 = !DILocation(line: 67, column: 5, scope: !904)
!910 = !DILocation(line: 71, column: 5, scope: !904)
!911 = !DILocation(line: 74, column: 5, scope: !904)
!912 = !DILocation(line: 77, column: 5, scope: !904)
!913 = !DILocation(line: 80, column: 5, scope: !904)
!914 = !DILocation(line: 82, column: 5, scope: !904)
!915 = !DILocation(line: 84, column: 5, scope: !904)
!916 = !DILocation(line: 86, column: 5, scope: !904)
!917 = !DILocation(line: 88, column: 5, scope: !904)
!918 = !DILocation(line: 90, column: 5, scope: !904)
!919 = !DILocation(line: 93, column: 5, scope: !904)
!920 = !DILocation(line: 96, column: 5, scope: !904)
!921 = !DILocation(line: 105, column: 5, scope: !904)
!922 = !DILocation(line: 109, column: 5, scope: !904)
!923 = !DILocation(line: 112, column: 5, scope: !904)
!924 = !DILocation(line: 114, column: 1, scope: !898)
!925 = distinct !DISubprogram(name: "report_error", linkageName: "_ZN7__ubsanL12report_errorEPKcS1_", scope: !224, file: !38, line: 35, type: !926, scopeLine: 36, flags: DIFlagPrototyped | DIFlagNoReturn, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!926 = !DISubroutineType(types: !927)
!927 = !{null, !239, !239}
!928 = !DILocalVariable(name: "msg", arg: 1, scope: !925, file: !38, line: 35, type: !239)
!929 = !DILocation(line: 35, column: 64, scope: !925)
!930 = !DILocalVariable(name: "suffix", arg: 2, scope: !925, file: !38, line: 36, type: !239)
!931 = !DILocation(line: 36, column: 64, scope: !925)
!932 = !DILocation(line: 37, column: 41, scope: !925)
!933 = !DILocation(line: 37, column: 46, scope: !925)
!934 = !DILocation(line: 37, column: 3, scope: !925)
!935 = distinct !DISubprogram(name: "__ubsan_handle_type_mismatch_v1_abort", scope: !38, file: !38, line: 180, type: !787, scopeLine: 181, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!936 = !DILocalVariable(name: "Data", arg: 1, scope: !935, file: !38, line: 180, type: !789)
!937 = !DILocation(line: 180, column: 73, scope: !935)
!938 = !DILocalVariable(name: "Pointer", arg: 2, scope: !935, file: !38, line: 181, type: !798)
!939 = !DILocation(line: 181, column: 67, scope: !935)
!940 = !DILocation(line: 183, column: 26, scope: !935)
!941 = !DILocation(line: 183, column: 32, scope: !935)
!942 = !DILocation(line: 183, column: 3, scope: !935)
!943 = !DILocation(line: 184, column: 1, scope: !935)
!944 = distinct !DISubprogram(name: "__ubsan_handle_alignment_assumption", scope: !38, file: !38, line: 195, type: !945, scopeLine: 197, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!945 = !DISubroutineType(types: !946)
!946 = !{null, !947, !798, !798, !798}
!947 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !948, size: 64)
!948 = !DICompositeType(tag: DW_TAG_structure_type, name: "AlignmentAssumptionData", file: !317, line: 32, size: 320, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS23AlignmentAssumptionData")
!949 = !DILocalVariable(name: "Data", arg: 1, scope: !944, file: !38, line: 195, type: !947)
!950 = !DILocation(line: 195, column: 62, scope: !944)
!951 = !DILocalVariable(name: "Pointer", arg: 2, scope: !944, file: !38, line: 196, type: !798)
!952 = !DILocation(line: 196, column: 49, scope: !944)
!953 = !DILocalVariable(name: "Alignment", arg: 3, scope: !944, file: !38, line: 196, type: !798)
!954 = !DILocation(line: 196, column: 70, scope: !944)
!955 = !DILocalVariable(name: "Offset", arg: 4, scope: !944, file: !38, line: 197, type: !798)
!956 = !DILocation(line: 197, column: 49, scope: !944)
!957 = !DILocation(line: 198, column: 33, scope: !944)
!958 = !DILocation(line: 198, column: 39, scope: !944)
!959 = !DILocation(line: 198, column: 48, scope: !944)
!960 = !DILocation(line: 198, column: 59, scope: !944)
!961 = !DILocation(line: 198, column: 3, scope: !944)
!962 = !DILocation(line: 199, column: 1, scope: !944)
!963 = distinct !DISubprogram(name: "handleAlignmentAssumptionImpl", linkageName: "_ZN7__ubsanL29handleAlignmentAssumptionImplEP23AlignmentAssumptionDatammm", scope: !224, file: !38, line: 186, type: !945, scopeLine: 189, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!964 = !DILocalVariable(arg: 1, scope: !963, file: !38, line: 186, type: !947)
!965 = !DILocation(line: 186, column: 77, scope: !963)
!966 = !DILocalVariable(arg: 2, scope: !963, file: !38, line: 187, type: !798)
!967 = !DILocation(line: 187, column: 66, scope: !963)
!968 = !DILocalVariable(arg: 3, scope: !963, file: !38, line: 188, type: !798)
!969 = !DILocation(line: 188, column: 68, scope: !963)
!970 = !DILocalVariable(arg: 4, scope: !963, file: !38, line: 189, type: !798)
!971 = !DILocation(line: 189, column: 65, scope: !963)
!972 = !DILocalVariable(name: "ET", scope: !963, file: !38, line: 190, type: !256)
!973 = !DILocation(line: 190, column: 13, scope: !963)
!974 = !DILocation(line: 191, column: 21, scope: !963)
!975 = !DILocation(line: 191, column: 3, scope: !963)
!976 = distinct !DISubprogram(name: "__ubsan_handle_alignment_assumption_abort", scope: !38, file: !38, line: 201, type: !945, scopeLine: 203, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!977 = !DILocalVariable(name: "Data", arg: 1, scope: !976, file: !38, line: 202, type: !947)
!978 = !DILocation(line: 202, column: 30, scope: !976)
!979 = !DILocalVariable(name: "Pointer", arg: 2, scope: !976, file: !38, line: 202, type: !798)
!980 = !DILocation(line: 202, column: 48, scope: !976)
!981 = !DILocalVariable(name: "Alignment", arg: 3, scope: !976, file: !38, line: 202, type: !798)
!982 = !DILocation(line: 202, column: 69, scope: !976)
!983 = !DILocalVariable(name: "Offset", arg: 4, scope: !976, file: !38, line: 203, type: !798)
!984 = !DILocation(line: 203, column: 17, scope: !976)
!985 = !DILocation(line: 204, column: 33, scope: !976)
!986 = !DILocation(line: 204, column: 39, scope: !976)
!987 = !DILocation(line: 204, column: 48, scope: !976)
!988 = !DILocation(line: 204, column: 59, scope: !976)
!989 = !DILocation(line: 204, column: 3, scope: !976)
!990 = !DILocation(line: 205, column: 1, scope: !976)
!991 = distinct !DISubprogram(name: "__ubsan_handle_add_overflow", scope: !38, file: !38, line: 222, type: !992, scopeLine: 222, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!992 = !DISubroutineType(types: !993)
!993 = !{null, !994, !798, !798}
!994 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !995, size: 64)
!995 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "OverflowData", file: !317, line: 38, size: 192, flags: DIFlagTypePassByValue | DIFlagNonTrivial, elements: !996, identifier: "_ZTS12OverflowData")
!996 = !{!997, !998}
!997 = !DIDerivedType(tag: DW_TAG_member, name: "Loc", scope: !995, file: !317, line: 39, baseType: !793, size: 128)
!998 = !DIDerivedType(tag: DW_TAG_member, name: "Type", scope: !995, file: !317, line: 40, baseType: !795, size: 64, offset: 128)
!999 = !DILocalVariable(name: "Data", arg: 1, scope: !991, file: !38, line: 222, type: !994)
!1000 = !DILocation(line: 222, column: 1, scope: !991)
!1001 = !DILocalVariable(name: "LHS", arg: 2, scope: !991, file: !38, line: 222, type: !798)
!1002 = !DILocalVariable(name: "RHS", arg: 3, scope: !991, file: !38, line: 222, type: !798)
!1003 = distinct !DISubprogram(name: "handleIntegerOverflowImpl", linkageName: "_ZN7__ubsanL25handleIntegerOverflowImplEP12OverflowDatamPKc", scope: !224, file: !38, line: 208, type: !1004, scopeLine: 209, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1004 = !DISubroutineType(types: !1005)
!1005 = !{null, !994, !798, !239}
!1006 = !DILocalVariable(name: "Data", arg: 1, scope: !1003, file: !38, line: 208, type: !994)
!1007 = !DILocation(line: 208, column: 53, scope: !1003)
!1008 = !DILocalVariable(arg: 2, scope: !1003, file: !38, line: 208, type: !798)
!1009 = !DILocation(line: 208, column: 78, scope: !1003)
!1010 = !DILocalVariable(arg: 3, scope: !1003, file: !38, line: 209, type: !239)
!1011 = !DILocation(line: 209, column: 64, scope: !1003)
!1012 = !DILocalVariable(name: "IsSigned", scope: !1003, file: !38, line: 210, type: !248)
!1013 = !DILocation(line: 210, column: 8, scope: !1003)
!1014 = !DILocation(line: 210, column: 19, scope: !1003)
!1015 = !DILocation(line: 210, column: 25, scope: !1003)
!1016 = !DILocation(line: 210, column: 30, scope: !1003)
!1017 = !DILocalVariable(name: "ET", scope: !1003, file: !38, line: 211, type: !256)
!1018 = !DILocation(line: 211, column: 13, scope: !1003)
!1019 = !DILocation(line: 211, column: 18, scope: !1003)
!1020 = !DILocation(line: 213, column: 21, scope: !1003)
!1021 = !DILocation(line: 213, column: 3, scope: !1003)
!1022 = distinct !DISubprogram(name: "isSignedIntegerTy", linkageName: "_ZNK7__ubsan14TypeDescriptor17isSignedIntegerTyEv", scope: !223, file: !222, line: 73, type: !246, scopeLine: 73, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, declaration: !249, retainedNodes: !334)
!1023 = !DILocalVariable(name: "this", arg: 1, scope: !1022, type: !1024, flags: DIFlagArtificial | DIFlagObjectPointer)
!1024 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !241, size: 64)
!1025 = !DILocation(line: 0, scope: !1022)
!1026 = !DILocation(line: 73, column: 43, scope: !1022)
!1027 = !DILocation(line: 73, column: 57, scope: !1022)
!1028 = !DILocation(line: 73, column: 61, scope: !1022)
!1029 = !DILocation(line: 73, column: 70, scope: !1022)
!1030 = !DILocation(line: 73, column: 60, scope: !1022)
!1031 = !DILocation(line: 73, column: 36, scope: !1022)
!1032 = distinct !DISubprogram(name: "isIntegerTy", linkageName: "_ZNK7__ubsan14TypeDescriptor11isIntegerTyEv", scope: !223, file: !222, line: 72, type: !246, scopeLine: 72, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, declaration: !245, retainedNodes: !334)
!1033 = !DILocalVariable(name: "this", arg: 1, scope: !1032, type: !1024, flags: DIFlagArtificial | DIFlagObjectPointer)
!1034 = !DILocation(line: 0, scope: !1032)
!1035 = !DILocation(line: 72, column: 37, scope: !1032)
!1036 = !DILocation(line: 72, column: 47, scope: !1032)
!1037 = !DILocation(line: 72, column: 30, scope: !1032)
!1038 = distinct !DISubprogram(name: "getKind", linkageName: "_ZNK7__ubsan14TypeDescriptor7getKindEv", scope: !223, file: !222, line: 70, type: !243, scopeLine: 70, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, declaration: !242, retainedNodes: !334)
!1039 = !DILocalVariable(name: "this", arg: 1, scope: !1038, type: !1024, flags: DIFlagArtificial | DIFlagObjectPointer)
!1040 = !DILocation(line: 0, scope: !1038)
!1041 = !DILocation(line: 70, column: 51, scope: !1038)
!1042 = !DILocation(line: 70, column: 33, scope: !1038)
!1043 = !DILocation(line: 70, column: 26, scope: !1038)
!1044 = distinct !DISubprogram(name: "__ubsan_handle_add_overflow_abort", scope: !38, file: !38, line: 223, type: !992, scopeLine: 223, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1045 = !DILocalVariable(name: "Data", arg: 1, scope: !1044, file: !38, line: 223, type: !994)
!1046 = !DILocation(line: 223, column: 1, scope: !1044)
!1047 = !DILocalVariable(name: "LHS", arg: 2, scope: !1044, file: !38, line: 223, type: !798)
!1048 = !DILocalVariable(name: "RHS", arg: 3, scope: !1044, file: !38, line: 223, type: !798)
!1049 = distinct !DISubprogram(name: "__ubsan_handle_sub_overflow", scope: !38, file: !38, line: 224, type: !992, scopeLine: 224, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1050 = !DILocalVariable(name: "Data", arg: 1, scope: !1049, file: !38, line: 224, type: !994)
!1051 = !DILocation(line: 224, column: 1, scope: !1049)
!1052 = !DILocalVariable(name: "LHS", arg: 2, scope: !1049, file: !38, line: 224, type: !798)
!1053 = !DILocalVariable(name: "RHS", arg: 3, scope: !1049, file: !38, line: 224, type: !798)
!1054 = distinct !DISubprogram(name: "__ubsan_handle_sub_overflow_abort", scope: !38, file: !38, line: 225, type: !992, scopeLine: 225, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1055 = !DILocalVariable(name: "Data", arg: 1, scope: !1054, file: !38, line: 225, type: !994)
!1056 = !DILocation(line: 225, column: 1, scope: !1054)
!1057 = !DILocalVariable(name: "LHS", arg: 2, scope: !1054, file: !38, line: 225, type: !798)
!1058 = !DILocalVariable(name: "RHS", arg: 3, scope: !1054, file: !38, line: 225, type: !798)
!1059 = distinct !DISubprogram(name: "__ubsan_handle_mul_overflow", scope: !38, file: !38, line: 226, type: !992, scopeLine: 226, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1060 = !DILocalVariable(name: "Data", arg: 1, scope: !1059, file: !38, line: 226, type: !994)
!1061 = !DILocation(line: 226, column: 1, scope: !1059)
!1062 = !DILocalVariable(name: "LHS", arg: 2, scope: !1059, file: !38, line: 226, type: !798)
!1063 = !DILocalVariable(name: "RHS", arg: 3, scope: !1059, file: !38, line: 226, type: !798)
!1064 = distinct !DISubprogram(name: "__ubsan_handle_mul_overflow_abort", scope: !38, file: !38, line: 227, type: !992, scopeLine: 227, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1065 = !DILocalVariable(name: "Data", arg: 1, scope: !1064, file: !38, line: 227, type: !994)
!1066 = !DILocation(line: 227, column: 1, scope: !1064)
!1067 = !DILocalVariable(name: "LHS", arg: 2, scope: !1064, file: !38, line: 227, type: !798)
!1068 = !DILocalVariable(name: "RHS", arg: 3, scope: !1064, file: !38, line: 227, type: !798)
!1069 = distinct !DISubprogram(name: "__ubsan_handle_negate_overflow", scope: !38, file: !38, line: 237, type: !1070, scopeLine: 238, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1070 = !DISubroutineType(types: !1071)
!1071 = !{null, !994, !798}
!1072 = !DILocalVariable(name: "Data", arg: 1, scope: !1069, file: !38, line: 237, type: !994)
!1073 = !DILocation(line: 237, column: 62, scope: !1069)
!1074 = !DILocalVariable(name: "OldVal", arg: 2, scope: !1069, file: !38, line: 238, type: !798)
!1075 = !DILocation(line: 238, column: 60, scope: !1069)
!1076 = !DILocation(line: 239, column: 28, scope: !1069)
!1077 = !DILocation(line: 239, column: 34, scope: !1069)
!1078 = !DILocation(line: 239, column: 3, scope: !1069)
!1079 = !DILocation(line: 240, column: 1, scope: !1069)
!1080 = distinct !DISubprogram(name: "handleNegateOverflowImpl", linkageName: "_ZN7__ubsanL24handleNegateOverflowImplEP12OverflowDatam", scope: !224, file: !38, line: 229, type: !1070, scopeLine: 230, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1081 = !DILocalVariable(name: "Data", arg: 1, scope: !1080, file: !38, line: 229, type: !994)
!1082 = !DILocation(line: 229, column: 52, scope: !1080)
!1083 = !DILocalVariable(arg: 2, scope: !1080, file: !38, line: 230, type: !798)
!1084 = !DILocation(line: 230, column: 60, scope: !1080)
!1085 = !DILocalVariable(name: "IsSigned", scope: !1080, file: !38, line: 231, type: !248)
!1086 = !DILocation(line: 231, column: 8, scope: !1080)
!1087 = !DILocation(line: 231, column: 19, scope: !1080)
!1088 = !DILocation(line: 231, column: 25, scope: !1080)
!1089 = !DILocation(line: 231, column: 30, scope: !1080)
!1090 = !DILocalVariable(name: "ET", scope: !1080, file: !38, line: 232, type: !256)
!1091 = !DILocation(line: 232, column: 13, scope: !1080)
!1092 = !DILocation(line: 232, column: 18, scope: !1080)
!1093 = !DILocation(line: 234, column: 21, scope: !1080)
!1094 = !DILocation(line: 234, column: 3, scope: !1080)
!1095 = distinct !DISubprogram(name: "__ubsan_handle_negate_overflow_abort", scope: !38, file: !38, line: 242, type: !1070, scopeLine: 243, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1096 = !DILocalVariable(name: "Data", arg: 1, scope: !1095, file: !38, line: 242, type: !994)
!1097 = !DILocation(line: 242, column: 68, scope: !1095)
!1098 = !DILocalVariable(name: "OldVal", arg: 2, scope: !1095, file: !38, line: 243, type: !798)
!1099 = !DILocation(line: 243, column: 66, scope: !1095)
!1100 = !DILocation(line: 244, column: 28, scope: !1095)
!1101 = !DILocation(line: 244, column: 34, scope: !1095)
!1102 = !DILocation(line: 244, column: 3, scope: !1095)
!1103 = !DILocation(line: 245, column: 1, scope: !1095)
!1104 = distinct !DISubprogram(name: "__ubsan_handle_divrem_overflow", scope: !38, file: !38, line: 257, type: !992, scopeLine: 259, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1105 = !DILocalVariable(name: "Data", arg: 1, scope: !1104, file: !38, line: 257, type: !994)
!1106 = !DILocation(line: 257, column: 62, scope: !1104)
!1107 = !DILocalVariable(name: "LHS", arg: 2, scope: !1104, file: !38, line: 258, type: !798)
!1108 = !DILocation(line: 258, column: 60, scope: !1104)
!1109 = !DILocalVariable(name: "RHS", arg: 3, scope: !1104, file: !38, line: 259, type: !798)
!1110 = !DILocation(line: 259, column: 60, scope: !1104)
!1111 = !DILocation(line: 260, column: 28, scope: !1104)
!1112 = !DILocation(line: 260, column: 34, scope: !1104)
!1113 = !DILocation(line: 260, column: 39, scope: !1104)
!1114 = !DILocation(line: 260, column: 3, scope: !1104)
!1115 = !DILocation(line: 261, column: 1, scope: !1104)
!1116 = distinct !DISubprogram(name: "handleDivremOverflowImpl", linkageName: "_ZN7__ubsanL24handleDivremOverflowImplEP12OverflowDatamm", scope: !224, file: !38, line: 247, type: !992, scopeLine: 248, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1117 = !DILocalVariable(name: "Data", arg: 1, scope: !1116, file: !38, line: 247, type: !994)
!1118 = !DILocation(line: 247, column: 52, scope: !1116)
!1119 = !DILocalVariable(arg: 2, scope: !1116, file: !38, line: 247, type: !798)
!1120 = !DILocation(line: 247, column: 77, scope: !1116)
!1121 = !DILocalVariable(arg: 3, scope: !1116, file: !38, line: 248, type: !798)
!1122 = !DILocation(line: 248, column: 57, scope: !1116)
!1123 = !DILocation(line: 249, column: 7, scope: !1124)
!1124 = distinct !DILexicalBlock(scope: !1116, file: !38, line: 249, column: 7)
!1125 = !DILocation(line: 249, column: 13, scope: !1124)
!1126 = !DILocation(line: 249, column: 18, scope: !1124)
!1127 = !DILocation(line: 249, column: 7, scope: !1116)
!1128 = !DILocation(line: 250, column: 5, scope: !1124)
!1129 = !DILocalVariable(name: "ET", scope: !1130, file: !38, line: 252, type: !256)
!1130 = distinct !DILexicalBlock(scope: !1124, file: !38, line: 251, column: 8)
!1131 = !DILocation(line: 252, column: 15, scope: !1130)
!1132 = !DILocation(line: 253, column: 23, scope: !1130)
!1133 = !DILocation(line: 253, column: 5, scope: !1130)
!1134 = distinct !DISubprogram(name: "__ubsan_handle_divrem_overflow_abort", scope: !38, file: !38, line: 263, type: !992, scopeLine: 265, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1135 = !DILocalVariable(name: "Data", arg: 1, scope: !1134, file: !38, line: 263, type: !994)
!1136 = !DILocation(line: 263, column: 68, scope: !1134)
!1137 = !DILocalVariable(name: "LHS", arg: 2, scope: !1134, file: !38, line: 264, type: !798)
!1138 = !DILocation(line: 264, column: 66, scope: !1134)
!1139 = !DILocalVariable(name: "RHS", arg: 3, scope: !1134, file: !38, line: 265, type: !798)
!1140 = !DILocation(line: 265, column: 66, scope: !1134)
!1141 = !DILocation(line: 266, column: 28, scope: !1134)
!1142 = !DILocation(line: 266, column: 34, scope: !1134)
!1143 = !DILocation(line: 266, column: 39, scope: !1134)
!1144 = !DILocation(line: 266, column: 3, scope: !1134)
!1145 = !DILocation(line: 267, column: 1, scope: !1134)
!1146 = distinct !DISubprogram(name: "__ubsan_handle_shift_out_of_bounds", scope: !38, file: !38, line: 275, type: !1147, scopeLine: 277, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1147 = !DISubroutineType(types: !1148)
!1148 = !{null, !1149, !798, !798}
!1149 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1150, size: 64)
!1150 = !DICompositeType(tag: DW_TAG_structure_type, name: "ShiftOutOfBoundsData", file: !317, line: 43, size: 256, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS20ShiftOutOfBoundsData")
!1151 = !DILocalVariable(name: "Data", arg: 1, scope: !1146, file: !38, line: 275, type: !1149)
!1152 = !DILocation(line: 275, column: 74, scope: !1146)
!1153 = !DILocalVariable(name: "LHS", arg: 2, scope: !1146, file: !38, line: 276, type: !798)
!1154 = !DILocation(line: 276, column: 64, scope: !1146)
!1155 = !DILocalVariable(name: "RHS", arg: 3, scope: !1146, file: !38, line: 277, type: !798)
!1156 = !DILocation(line: 277, column: 64, scope: !1146)
!1157 = !DILocation(line: 278, column: 30, scope: !1146)
!1158 = !DILocation(line: 278, column: 36, scope: !1146)
!1159 = !DILocation(line: 278, column: 41, scope: !1146)
!1160 = !DILocation(line: 278, column: 3, scope: !1146)
!1161 = !DILocation(line: 279, column: 1, scope: !1146)
!1162 = distinct !DISubprogram(name: "handleShiftOutOfBoundsImpl", linkageName: "_ZN7__ubsanL26handleShiftOutOfBoundsImplEP20ShiftOutOfBoundsDatamm", scope: !224, file: !38, line: 269, type: !1147, scopeLine: 271, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1163 = !DILocalVariable(arg: 1, scope: !1162, file: !38, line: 269, type: !1149)
!1164 = !DILocation(line: 269, column: 71, scope: !1162)
!1165 = !DILocalVariable(arg: 2, scope: !1162, file: !38, line: 270, type: !798)
!1166 = !DILocation(line: 270, column: 59, scope: !1162)
!1167 = !DILocalVariable(arg: 3, scope: !1162, file: !38, line: 271, type: !798)
!1168 = !DILocation(line: 271, column: 59, scope: !1162)
!1169 = !DILocation(line: 272, column: 3, scope: !1162)
!1170 = distinct !DISubprogram(name: "__ubsan_handle_shift_out_of_bounds_abort", scope: !38, file: !38, line: 282, type: !1147, scopeLine: 283, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1171 = !DILocalVariable(name: "Data", arg: 1, scope: !1170, file: !38, line: 282, type: !1149)
!1172 = !DILocation(line: 282, column: 64, scope: !1170)
!1173 = !DILocalVariable(name: "LHS", arg: 2, scope: !1170, file: !38, line: 283, type: !798)
!1174 = !DILocation(line: 283, column: 54, scope: !1170)
!1175 = !DILocalVariable(name: "RHS", arg: 3, scope: !1170, file: !38, line: 283, type: !798)
!1176 = !DILocation(line: 283, column: 71, scope: !1170)
!1177 = !DILocation(line: 284, column: 30, scope: !1170)
!1178 = !DILocation(line: 284, column: 36, scope: !1170)
!1179 = !DILocation(line: 284, column: 41, scope: !1170)
!1180 = !DILocation(line: 284, column: 3, scope: !1170)
!1181 = !DILocation(line: 285, column: 1, scope: !1170)
!1182 = distinct !DISubprogram(name: "__ubsan_handle_out_of_bounds", scope: !38, file: !38, line: 293, type: !1183, scopeLine: 294, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1183 = !DISubroutineType(types: !1184)
!1184 = !{null, !1185, !798}
!1185 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1186, size: 64)
!1186 = !DICompositeType(tag: DW_TAG_structure_type, name: "OutOfBoundsData", file: !317, line: 49, size: 256, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS15OutOfBoundsData")
!1187 = !DILocalVariable(name: "Data", arg: 1, scope: !1182, file: !38, line: 293, type: !1185)
!1188 = !DILocation(line: 293, column: 63, scope: !1182)
!1189 = !DILocalVariable(name: "Index", arg: 2, scope: !1182, file: !38, line: 294, type: !798)
!1190 = !DILocation(line: 294, column: 58, scope: !1182)
!1191 = !DILocation(line: 295, column: 25, scope: !1182)
!1192 = !DILocation(line: 295, column: 31, scope: !1182)
!1193 = !DILocation(line: 295, column: 3, scope: !1182)
!1194 = !DILocation(line: 296, column: 1, scope: !1182)
!1195 = distinct !DISubprogram(name: "handleOutOfBoundsImpl", linkageName: "_ZN7__ubsanL21handleOutOfBoundsImplEP15OutOfBoundsDatam", scope: !224, file: !38, line: 287, type: !1183, scopeLine: 288, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1196 = !DILocalVariable(arg: 1, scope: !1195, file: !38, line: 287, type: !1185)
!1197 = !DILocation(line: 287, column: 61, scope: !1195)
!1198 = !DILocalVariable(arg: 2, scope: !1195, file: !38, line: 288, type: !798)
!1199 = !DILocation(line: 288, column: 56, scope: !1195)
!1200 = !DILocalVariable(name: "ET", scope: !1195, file: !38, line: 289, type: !256)
!1201 = !DILocation(line: 289, column: 13, scope: !1195)
!1202 = !DILocation(line: 290, column: 21, scope: !1195)
!1203 = !DILocation(line: 290, column: 3, scope: !1195)
!1204 = distinct !DISubprogram(name: "__ubsan_handle_out_of_bounds_abort", scope: !38, file: !38, line: 298, type: !1183, scopeLine: 299, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1205 = !DILocalVariable(name: "Data", arg: 1, scope: !1204, file: !38, line: 298, type: !1185)
!1206 = !DILocation(line: 298, column: 69, scope: !1204)
!1207 = !DILocalVariable(name: "Index", arg: 2, scope: !1204, file: !38, line: 299, type: !798)
!1208 = !DILocation(line: 299, column: 64, scope: !1204)
!1209 = !DILocation(line: 300, column: 25, scope: !1204)
!1210 = !DILocation(line: 300, column: 31, scope: !1204)
!1211 = !DILocation(line: 300, column: 3, scope: !1204)
!1212 = !DILocation(line: 301, column: 1, scope: !1204)
!1213 = distinct !DISubprogram(name: "__ubsan_handle_builtin_unreachable", scope: !38, file: !38, line: 308, type: !1214, scopeLine: 308, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1214 = !DISubroutineType(types: !1215)
!1215 = !{null, !1216}
!1216 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1217, size: 64)
!1217 = !DICompositeType(tag: DW_TAG_structure_type, name: "UnreachableData", file: !317, line: 55, size: 128, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS15UnreachableData")
!1218 = !DILocalVariable(name: "Data", arg: 1, scope: !1213, file: !38, line: 308, type: !1216)
!1219 = !DILocation(line: 308, column: 69, scope: !1213)
!1220 = !DILocation(line: 309, column: 32, scope: !1213)
!1221 = !DILocation(line: 309, column: 3, scope: !1213)
!1222 = !DILocation(line: 310, column: 1, scope: !1213)
!1223 = distinct !DISubprogram(name: "handleBuiltinUnreachableImpl", linkageName: "_ZN7__ubsanL28handleBuiltinUnreachableImplEP15UnreachableData", scope: !224, file: !38, line: 303, type: !1214, scopeLine: 303, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1224 = !DILocalVariable(arg: 1, scope: !1223, file: !38, line: 303, type: !1216)
!1225 = !DILocation(line: 303, column: 68, scope: !1223)
!1226 = !DILocalVariable(name: "ET", scope: !1223, file: !38, line: 304, type: !256)
!1227 = !DILocation(line: 304, column: 13, scope: !1223)
!1228 = !DILocation(line: 305, column: 21, scope: !1223)
!1229 = !DILocation(line: 305, column: 3, scope: !1223)
!1230 = distinct !DISubprogram(name: "__ubsan_handle_missing_return", scope: !38, file: !38, line: 317, type: !1214, scopeLine: 317, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1231 = !DILocalVariable(name: "Data", arg: 1, scope: !1230, file: !38, line: 317, type: !1216)
!1232 = !DILocation(line: 317, column: 64, scope: !1230)
!1233 = !DILocation(line: 318, column: 27, scope: !1230)
!1234 = !DILocation(line: 318, column: 3, scope: !1230)
!1235 = !DILocation(line: 319, column: 1, scope: !1230)
!1236 = distinct !DISubprogram(name: "handleMissingReturnImpl", linkageName: "_ZN7__ubsanL23handleMissingReturnImplEP15UnreachableData", scope: !224, file: !38, line: 312, type: !1214, scopeLine: 312, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1237 = !DILocalVariable(arg: 1, scope: !1236, file: !38, line: 312, type: !1216)
!1238 = !DILocation(line: 312, column: 63, scope: !1236)
!1239 = !DILocalVariable(name: "ET", scope: !1236, file: !38, line: 313, type: !256)
!1240 = !DILocation(line: 313, column: 13, scope: !1236)
!1241 = !DILocation(line: 314, column: 21, scope: !1236)
!1242 = !DILocation(line: 314, column: 3, scope: !1236)
!1243 = distinct !DISubprogram(name: "__ubsan_handle_vla_bound_not_positive", scope: !38, file: !38, line: 327, type: !1244, scopeLine: 328, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1244 = !DISubroutineType(types: !1245)
!1245 = !{null, !1246, !798}
!1246 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1247, size: 64)
!1247 = !DICompositeType(tag: DW_TAG_structure_type, name: "VLABoundData", file: !317, line: 59, size: 192, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS12VLABoundData")
!1248 = !DILocalVariable(name: "Data", arg: 1, scope: !1243, file: !38, line: 327, type: !1246)
!1249 = !DILocation(line: 327, column: 69, scope: !1243)
!1250 = !DILocalVariable(name: "Bound", arg: 2, scope: !1243, file: !38, line: 328, type: !798)
!1251 = !DILocation(line: 328, column: 67, scope: !1243)
!1252 = !DILocation(line: 329, column: 29, scope: !1243)
!1253 = !DILocation(line: 329, column: 35, scope: !1243)
!1254 = !DILocation(line: 329, column: 3, scope: !1243)
!1255 = !DILocation(line: 330, column: 1, scope: !1243)
!1256 = distinct !DISubprogram(name: "handleVLABoundNotPositive", linkageName: "_ZN7__ubsanL25handleVLABoundNotPositiveEP12VLABoundDatam", scope: !224, file: !38, line: 321, type: !1244, scopeLine: 322, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1257 = !DILocalVariable(arg: 1, scope: !1256, file: !38, line: 321, type: !1246)
!1258 = !DILocation(line: 321, column: 62, scope: !1256)
!1259 = !DILocalVariable(arg: 2, scope: !1256, file: !38, line: 322, type: !798)
!1260 = !DILocation(line: 322, column: 60, scope: !1256)
!1261 = !DILocalVariable(name: "ET", scope: !1256, file: !38, line: 323, type: !256)
!1262 = !DILocation(line: 323, column: 13, scope: !1256)
!1263 = !DILocation(line: 324, column: 21, scope: !1256)
!1264 = !DILocation(line: 324, column: 3, scope: !1256)
!1265 = distinct !DISubprogram(name: "__ubsan_handle_vla_bound_not_positive_abort", scope: !38, file: !38, line: 332, type: !1244, scopeLine: 333, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1266 = !DILocalVariable(name: "Data", arg: 1, scope: !1265, file: !38, line: 332, type: !1246)
!1267 = !DILocation(line: 332, column: 75, scope: !1265)
!1268 = !DILocalVariable(name: "Bound", arg: 2, scope: !1265, file: !38, line: 333, type: !798)
!1269 = !DILocation(line: 333, column: 73, scope: !1265)
!1270 = !DILocation(line: 334, column: 29, scope: !1265)
!1271 = !DILocation(line: 334, column: 35, scope: !1265)
!1272 = !DILocation(line: 334, column: 3, scope: !1265)
!1273 = !DILocation(line: 335, column: 1, scope: !1265)
!1274 = distinct !DISubprogram(name: "__ubsan_handle_float_cast_overflow", scope: !38, file: !38, line: 342, type: !1275, scopeLine: 343, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1275 = !DISubroutineType(types: !1276)
!1276 = !{null, !1277, !798}
!1277 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)
!1278 = !DILocalVariable(name: "Data", arg: 1, scope: !1274, file: !38, line: 342, type: !1277)
!1279 = !DILocation(line: 342, column: 58, scope: !1274)
!1280 = !DILocalVariable(name: "From", arg: 2, scope: !1274, file: !38, line: 343, type: !798)
!1281 = !DILocation(line: 343, column: 64, scope: !1274)
!1282 = !DILocation(line: 344, column: 27, scope: !1274)
!1283 = !DILocation(line: 344, column: 33, scope: !1274)
!1284 = !DILocation(line: 344, column: 3, scope: !1274)
!1285 = !DILocation(line: 345, column: 1, scope: !1274)
!1286 = distinct !DISubprogram(name: "handleFloatCastOverflow", linkageName: "_ZN7__ubsanL23handleFloatCastOverflowEPvm", scope: !224, file: !38, line: 337, type: !1275, scopeLine: 337, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1287 = !DILocalVariable(arg: 1, scope: !1286, file: !38, line: 337, type: !1277)
!1288 = !DILocation(line: 337, column: 55, scope: !1286)
!1289 = !DILocalVariable(arg: 2, scope: !1286, file: !38, line: 337, type: !798)
!1290 = !DILocation(line: 337, column: 77, scope: !1286)
!1291 = !DILocalVariable(name: "ET", scope: !1286, file: !38, line: 338, type: !256)
!1292 = !DILocation(line: 338, column: 13, scope: !1286)
!1293 = !DILocation(line: 339, column: 21, scope: !1286)
!1294 = !DILocation(line: 339, column: 3, scope: !1286)
!1295 = distinct !DISubprogram(name: "__ubsan_handle_float_cast_overflow_abort", scope: !38, file: !38, line: 347, type: !1275, scopeLine: 348, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1296 = !DILocalVariable(name: "Data", arg: 1, scope: !1295, file: !38, line: 347, type: !1277)
!1297 = !DILocation(line: 347, column: 64, scope: !1295)
!1298 = !DILocalVariable(name: "From", arg: 2, scope: !1295, file: !38, line: 348, type: !798)
!1299 = !DILocation(line: 348, column: 70, scope: !1295)
!1300 = !DILocation(line: 349, column: 27, scope: !1295)
!1301 = !DILocation(line: 349, column: 33, scope: !1295)
!1302 = !DILocation(line: 349, column: 3, scope: !1295)
!1303 = !DILocation(line: 350, column: 1, scope: !1295)
!1304 = distinct !DISubprogram(name: "__ubsan_handle_load_invalid_value", scope: !38, file: !38, line: 357, type: !1305, scopeLine: 358, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1305 = !DISubroutineType(types: !1306)
!1306 = !{null, !1307, !798}
!1307 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1308, size: 64)
!1308 = !DICompositeType(tag: DW_TAG_structure_type, name: "InvalidValueData", file: !317, line: 64, size: 192, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS16InvalidValueData")
!1309 = !DILocalVariable(name: "Data", arg: 1, scope: !1304, file: !38, line: 357, type: !1307)
!1310 = !DILocation(line: 357, column: 69, scope: !1304)
!1311 = !DILocalVariable(name: "Val", arg: 2, scope: !1304, file: !38, line: 358, type: !798)
!1312 = !DILocation(line: 358, column: 63, scope: !1304)
!1313 = !DILocation(line: 359, column: 26, scope: !1304)
!1314 = !DILocation(line: 359, column: 32, scope: !1304)
!1315 = !DILocation(line: 359, column: 3, scope: !1304)
!1316 = !DILocation(line: 360, column: 1, scope: !1304)
!1317 = distinct !DISubprogram(name: "handleLoadInvalidValue", linkageName: "_ZN7__ubsanL22handleLoadInvalidValueEP16InvalidValueDatam", scope: !224, file: !38, line: 352, type: !1305, scopeLine: 353, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1318 = !DILocalVariable(arg: 1, scope: !1317, file: !38, line: 352, type: !1307)
!1319 = !DILocation(line: 352, column: 63, scope: !1317)
!1320 = !DILocalVariable(arg: 2, scope: !1317, file: !38, line: 353, type: !798)
!1321 = !DILocation(line: 353, column: 55, scope: !1317)
!1322 = !DILocation(line: 354, column: 3, scope: !1317)
!1323 = distinct !DISubprogram(name: "__ubsan_handle_load_invalid_value_abort", scope: !38, file: !38, line: 361, type: !1305, scopeLine: 362, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1324 = !DILocalVariable(name: "Data", arg: 1, scope: !1323, file: !38, line: 361, type: !1307)
!1325 = !DILocation(line: 361, column: 75, scope: !1323)
!1326 = !DILocalVariable(name: "Val", arg: 2, scope: !1323, file: !38, line: 362, type: !798)
!1327 = !DILocation(line: 362, column: 69, scope: !1323)
!1328 = !DILocation(line: 363, column: 26, scope: !1323)
!1329 = !DILocation(line: 363, column: 32, scope: !1323)
!1330 = !DILocation(line: 363, column: 3, scope: !1323)
!1331 = !DILocation(line: 364, column: 1, scope: !1323)
!1332 = distinct !DISubprogram(name: "__ubsan_handle_implicit_conversion", scope: !38, file: !38, line: 404, type: !1333, scopeLine: 406, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1333 = !DISubroutineType(types: !1334)
!1334 = !{null, !1335, !798, !798}
!1335 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1336, size: 64)
!1336 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ImplicitConversionData", file: !317, line: 79, size: 320, flags: DIFlagTypePassByValue | DIFlagNonTrivial, elements: !1337, identifier: "_ZTS22ImplicitConversionData")
!1337 = !{!1338, !1339, !1340, !1341}
!1338 = !DIDerivedType(tag: DW_TAG_member, name: "Loc", scope: !1336, file: !317, line: 80, baseType: !793, size: 128)
!1339 = !DIDerivedType(tag: DW_TAG_member, name: "FromType", scope: !1336, file: !317, line: 81, baseType: !795, size: 64, offset: 128)
!1340 = !DIDerivedType(tag: DW_TAG_member, name: "ToType", scope: !1336, file: !317, line: 82, baseType: !795, size: 64, offset: 192)
!1341 = !DIDerivedType(tag: DW_TAG_member, name: "Kind", scope: !1336, file: !317, line: 83, baseType: !781, size: 8, offset: 256)
!1342 = !DILocalVariable(name: "Data", arg: 1, scope: !1332, file: !38, line: 404, type: !1335)
!1343 = !DILocation(line: 404, column: 76, scope: !1332)
!1344 = !DILocalVariable(name: "Src", arg: 2, scope: !1332, file: !38, line: 405, type: !798)
!1345 = !DILocation(line: 405, column: 64, scope: !1332)
!1346 = !DILocalVariable(name: "Dst", arg: 3, scope: !1332, file: !38, line: 406, type: !798)
!1347 = !DILocation(line: 406, column: 64, scope: !1332)
!1348 = !DILocation(line: 407, column: 28, scope: !1332)
!1349 = !DILocation(line: 407, column: 34, scope: !1332)
!1350 = !DILocation(line: 407, column: 39, scope: !1332)
!1351 = !DILocation(line: 407, column: 3, scope: !1332)
!1352 = !DILocation(line: 408, column: 1, scope: !1332)
!1353 = distinct !DISubprogram(name: "handleImplicitConversion", linkageName: "_ZN7__ubsanL24handleImplicitConversionEP22ImplicitConversionDatamm", scope: !224, file: !38, line: 366, type: !1333, scopeLine: 367, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1354 = !DILocalVariable(name: "Data", arg: 1, scope: !1353, file: !38, line: 366, type: !1335)
!1355 = !DILocation(line: 366, column: 62, scope: !1353)
!1356 = !DILocalVariable(arg: 2, scope: !1353, file: !38, line: 367, type: !798)
!1357 = !DILocation(line: 367, column: 57, scope: !1353)
!1358 = !DILocalVariable(arg: 3, scope: !1353, file: !38, line: 367, type: !798)
!1359 = !DILocation(line: 367, column: 78, scope: !1353)
!1360 = !DILocalVariable(name: "ET", scope: !1353, file: !38, line: 368, type: !256)
!1361 = !DILocation(line: 368, column: 13, scope: !1353)
!1362 = !DILocalVariable(name: "SrcTy", scope: !1353, file: !38, line: 370, type: !795)
!1363 = !DILocation(line: 370, column: 25, scope: !1353)
!1364 = !DILocation(line: 370, column: 33, scope: !1353)
!1365 = !DILocation(line: 370, column: 39, scope: !1353)
!1366 = !DILocalVariable(name: "DstTy", scope: !1353, file: !38, line: 371, type: !795)
!1367 = !DILocation(line: 371, column: 25, scope: !1353)
!1368 = !DILocation(line: 371, column: 33, scope: !1353)
!1369 = !DILocation(line: 371, column: 39, scope: !1353)
!1370 = !DILocalVariable(name: "SrcSigned", scope: !1353, file: !38, line: 373, type: !248)
!1371 = !DILocation(line: 373, column: 8, scope: !1353)
!1372 = !DILocation(line: 373, column: 20, scope: !1353)
!1373 = !DILocation(line: 373, column: 26, scope: !1353)
!1374 = !DILocalVariable(name: "DstSigned", scope: !1353, file: !38, line: 374, type: !248)
!1375 = !DILocation(line: 374, column: 8, scope: !1353)
!1376 = !DILocation(line: 374, column: 20, scope: !1353)
!1377 = !DILocation(line: 374, column: 26, scope: !1353)
!1378 = !DILocation(line: 376, column: 11, scope: !1353)
!1379 = !DILocation(line: 376, column: 17, scope: !1353)
!1380 = !DILocation(line: 376, column: 3, scope: !1353)
!1381 = !DILocation(line: 381, column: 10, scope: !1382)
!1382 = distinct !DILexicalBlock(scope: !1383, file: !38, line: 381, column: 9)
!1383 = distinct !DILexicalBlock(scope: !1384, file: !38, line: 377, column: 32)
!1384 = distinct !DILexicalBlock(scope: !1353, file: !38, line: 376, column: 23)
!1385 = !DILocation(line: 381, column: 20, scope: !1382)
!1386 = !DILocation(line: 381, column: 24, scope: !1382)
!1387 = !DILocation(line: 381, column: 9, scope: !1383)
!1388 = !DILocation(line: 382, column: 10, scope: !1389)
!1389 = distinct !DILexicalBlock(scope: !1382, file: !38, line: 381, column: 35)
!1390 = !DILocation(line: 383, column: 5, scope: !1389)
!1391 = !DILocation(line: 384, column: 10, scope: !1392)
!1392 = distinct !DILexicalBlock(scope: !1382, file: !38, line: 383, column: 12)
!1393 = !DILocation(line: 389, column: 8, scope: !1384)
!1394 = !DILocation(line: 390, column: 5, scope: !1384)
!1395 = !DILocation(line: 392, column: 8, scope: !1384)
!1396 = !DILocation(line: 393, column: 5, scope: !1384)
!1397 = !DILocation(line: 395, column: 8, scope: !1384)
!1398 = !DILocation(line: 396, column: 5, scope: !1384)
!1399 = !DILocation(line: 398, column: 8, scope: !1384)
!1400 = !DILocation(line: 399, column: 5, scope: !1384)
!1401 = !DILocation(line: 401, column: 21, scope: !1353)
!1402 = !DILocation(line: 401, column: 3, scope: !1353)
!1403 = distinct !DISubprogram(name: "__ubsan_handle_implicit_conversion_abort", scope: !38, file: !38, line: 411, type: !1333, scopeLine: 412, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1404 = !DILocalVariable(name: "Data", arg: 1, scope: !1403, file: !38, line: 411, type: !1335)
!1405 = !DILocation(line: 411, column: 66, scope: !1403)
!1406 = !DILocalVariable(name: "Src", arg: 2, scope: !1403, file: !38, line: 412, type: !798)
!1407 = !DILocation(line: 412, column: 54, scope: !1403)
!1408 = !DILocalVariable(name: "Dst", arg: 3, scope: !1403, file: !38, line: 412, type: !798)
!1409 = !DILocation(line: 412, column: 71, scope: !1403)
!1410 = !DILocation(line: 413, column: 28, scope: !1403)
!1411 = !DILocation(line: 413, column: 34, scope: !1403)
!1412 = !DILocation(line: 413, column: 39, scope: !1403)
!1413 = !DILocation(line: 413, column: 3, scope: !1403)
!1414 = !DILocation(line: 414, column: 1, scope: !1403)
!1415 = distinct !DISubprogram(name: "__ubsan_handle_invalid_builtin", scope: !38, file: !38, line: 421, type: !1416, scopeLine: 421, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1416 = !DISubroutineType(types: !1417)
!1417 = !{null, !1418}
!1418 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1419, size: 64)
!1419 = !DICompositeType(tag: DW_TAG_structure_type, name: "InvalidBuiltinData", file: !317, line: 86, size: 192, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS18InvalidBuiltinData")
!1420 = !DILocalVariable(name: "Data", arg: 1, scope: !1415, file: !38, line: 421, type: !1418)
!1421 = !DILocation(line: 421, column: 68, scope: !1415)
!1422 = !DILocation(line: 422, column: 24, scope: !1415)
!1423 = !DILocation(line: 422, column: 3, scope: !1415)
!1424 = !DILocation(line: 423, column: 1, scope: !1415)
!1425 = distinct !DISubprogram(name: "handleInvalidBuiltin", linkageName: "_ZN7__ubsanL20handleInvalidBuiltinEP18InvalidBuiltinData", scope: !224, file: !38, line: 416, type: !1416, scopeLine: 416, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1426 = !DILocalVariable(arg: 1, scope: !1425, file: !38, line: 416, type: !1418)
!1427 = !DILocation(line: 416, column: 63, scope: !1425)
!1428 = !DILocalVariable(name: "ET", scope: !1425, file: !38, line: 417, type: !256)
!1429 = !DILocation(line: 417, column: 13, scope: !1425)
!1430 = !DILocation(line: 418, column: 21, scope: !1425)
!1431 = !DILocation(line: 418, column: 3, scope: !1425)
!1432 = distinct !DISubprogram(name: "__ubsan_handle_invalid_builtin_abort", scope: !38, file: !38, line: 425, type: !1416, scopeLine: 425, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1433 = !DILocalVariable(name: "Data", arg: 1, scope: !1432, file: !38, line: 425, type: !1418)
!1434 = !DILocation(line: 425, column: 74, scope: !1432)
!1435 = !DILocation(line: 426, column: 24, scope: !1432)
!1436 = !DILocation(line: 426, column: 3, scope: !1432)
!1437 = !DILocation(line: 427, column: 1, scope: !1432)
!1438 = distinct !DISubprogram(name: "__ubsan_handle_nonnull_return_v1", scope: !38, file: !38, line: 436, type: !1439, scopeLine: 437, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1439 = !DISubroutineType(types: !1440)
!1440 = !{null, !1441, !1443}
!1441 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1442, size: 64)
!1442 = !DICompositeType(tag: DW_TAG_structure_type, name: "NonNullReturnData", file: !317, line: 91, size: 128, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS17NonNullReturnData")
!1443 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !793, size: 64)
!1444 = !DILocalVariable(name: "Data", arg: 1, scope: !1438, file: !38, line: 436, type: !1441)
!1445 = !DILocation(line: 436, column: 69, scope: !1438)
!1446 = !DILocalVariable(name: "LocPtr", arg: 2, scope: !1438, file: !38, line: 437, type: !1443)
!1447 = !DILocation(line: 437, column: 66, scope: !1438)
!1448 = !DILocation(line: 438, column: 23, scope: !1438)
!1449 = !DILocation(line: 438, column: 29, scope: !1438)
!1450 = !DILocation(line: 438, column: 3, scope: !1438)
!1451 = !DILocation(line: 439, column: 1, scope: !1438)
!1452 = distinct !DISubprogram(name: "handleNonNullReturn", linkageName: "_ZN7__ubsanL19handleNonNullReturnEP17NonNullReturnDataPNS_14SourceLocationEb", scope: !224, file: !38, line: 429, type: !1453, scopeLine: 430, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1453 = !DISubroutineType(types: !1454)
!1454 = !{null, !1441, !1443, !248}
!1455 = !DILocalVariable(arg: 1, scope: !1452, file: !38, line: 429, type: !1441)
!1456 = !DILocation(line: 429, column: 61, scope: !1452)
!1457 = !DILocalVariable(arg: 2, scope: !1452, file: !38, line: 430, type: !1443)
!1458 = !DILocation(line: 430, column: 60, scope: !1452)
!1459 = !DILocalVariable(name: "IsAttr", arg: 3, scope: !1452, file: !38, line: 430, type: !248)
!1460 = !DILocation(line: 430, column: 67, scope: !1452)
!1461 = !DILocalVariable(name: "ET", scope: !1452, file: !38, line: 431, type: !256)
!1462 = !DILocation(line: 431, column: 13, scope: !1452)
!1463 = !DILocation(line: 431, column: 18, scope: !1452)
!1464 = !DILocation(line: 433, column: 21, scope: !1452)
!1465 = !DILocation(line: 433, column: 3, scope: !1452)
!1466 = distinct !DISubprogram(name: "__ubsan_handle_nonnull_return_v1_abort", scope: !38, file: !38, line: 441, type: !1439, scopeLine: 442, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1467 = !DILocalVariable(name: "Data", arg: 1, scope: !1466, file: !38, line: 441, type: !1441)
!1468 = !DILocation(line: 441, column: 75, scope: !1466)
!1469 = !DILocalVariable(name: "LocPtr", arg: 2, scope: !1466, file: !38, line: 442, type: !1443)
!1470 = !DILocation(line: 442, column: 72, scope: !1466)
!1471 = !DILocation(line: 443, column: 23, scope: !1466)
!1472 = !DILocation(line: 443, column: 29, scope: !1466)
!1473 = !DILocation(line: 443, column: 3, scope: !1466)
!1474 = !DILocation(line: 444, column: 1, scope: !1466)
!1475 = distinct !DISubprogram(name: "__ubsan_handle_nullability_return_v1", scope: !38, file: !38, line: 446, type: !1439, scopeLine: 447, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1476 = !DILocalVariable(name: "Data", arg: 1, scope: !1475, file: !38, line: 446, type: !1441)
!1477 = !DILocation(line: 446, column: 73, scope: !1475)
!1478 = !DILocalVariable(name: "LocPtr", arg: 2, scope: !1475, file: !38, line: 447, type: !1443)
!1479 = !DILocation(line: 447, column: 70, scope: !1475)
!1480 = !DILocation(line: 448, column: 23, scope: !1475)
!1481 = !DILocation(line: 448, column: 29, scope: !1475)
!1482 = !DILocation(line: 448, column: 3, scope: !1475)
!1483 = !DILocation(line: 449, column: 1, scope: !1475)
!1484 = distinct !DISubprogram(name: "__ubsan_handle_nullability_return_v1_abort", scope: !38, file: !38, line: 452, type: !1439, scopeLine: 453, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1485 = !DILocalVariable(name: "Data", arg: 1, scope: !1484, file: !38, line: 452, type: !1441)
!1486 = !DILocation(line: 452, column: 63, scope: !1484)
!1487 = !DILocalVariable(name: "LocPtr", arg: 2, scope: !1484, file: !38, line: 453, type: !1443)
!1488 = !DILocation(line: 453, column: 60, scope: !1484)
!1489 = !DILocation(line: 454, column: 23, scope: !1484)
!1490 = !DILocation(line: 454, column: 29, scope: !1484)
!1491 = !DILocation(line: 454, column: 3, scope: !1484)
!1492 = !DILocation(line: 455, column: 1, scope: !1484)
!1493 = distinct !DISubprogram(name: "__ubsan_handle_nonnull_arg", scope: !38, file: !38, line: 463, type: !1494, scopeLine: 463, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1494 = !DISubroutineType(types: !1495)
!1495 = !{null, !1496}
!1496 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1497, size: 64)
!1497 = !DICompositeType(tag: DW_TAG_structure_type, name: "NonNullArgData", file: !317, line: 95, size: 320, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS14NonNullArgData")
!1498 = !DILocalVariable(name: "Data", arg: 1, scope: !1493, file: !38, line: 463, type: !1496)
!1499 = !DILocation(line: 463, column: 60, scope: !1493)
!1500 = !DILocation(line: 464, column: 20, scope: !1493)
!1501 = !DILocation(line: 464, column: 3, scope: !1493)
!1502 = !DILocation(line: 465, column: 1, scope: !1493)
!1503 = distinct !DISubprogram(name: "handleNonNullArg", linkageName: "_ZN7__ubsanL16handleNonNullArgEP14NonNullArgDatab", scope: !224, file: !38, line: 457, type: !1504, scopeLine: 457, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1504 = !DISubroutineType(types: !1505)
!1505 = !{null, !1496, !248}
!1506 = !DILocalVariable(arg: 1, scope: !1503, file: !38, line: 457, type: !1496)
!1507 = !DILocation(line: 457, column: 55, scope: !1503)
!1508 = !DILocalVariable(name: "IsAttr", arg: 2, scope: !1503, file: !38, line: 457, type: !248)
!1509 = !DILocation(line: 457, column: 62, scope: !1503)
!1510 = !DILocalVariable(name: "ET", scope: !1503, file: !38, line: 458, type: !256)
!1511 = !DILocation(line: 458, column: 13, scope: !1503)
!1512 = !DILocation(line: 458, column: 18, scope: !1503)
!1513 = !DILocation(line: 460, column: 21, scope: !1503)
!1514 = !DILocation(line: 460, column: 3, scope: !1503)
!1515 = distinct !DISubprogram(name: "__ubsan_handle_nonnull_arg_abort", scope: !38, file: !38, line: 467, type: !1494, scopeLine: 467, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1516 = !DILocalVariable(name: "Data", arg: 1, scope: !1515, file: !38, line: 467, type: !1496)
!1517 = !DILocation(line: 467, column: 66, scope: !1515)
!1518 = !DILocation(line: 468, column: 20, scope: !1515)
!1519 = !DILocation(line: 468, column: 3, scope: !1515)
!1520 = !DILocation(line: 469, column: 1, scope: !1515)
!1521 = distinct !DISubprogram(name: "__ubsan_handle_nullability_arg", scope: !38, file: !38, line: 471, type: !1494, scopeLine: 471, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1522 = !DILocalVariable(name: "Data", arg: 1, scope: !1521, file: !38, line: 471, type: !1496)
!1523 = !DILocation(line: 471, column: 64, scope: !1521)
!1524 = !DILocation(line: 472, column: 20, scope: !1521)
!1525 = !DILocation(line: 472, column: 3, scope: !1521)
!1526 = !DILocation(line: 473, column: 1, scope: !1521)
!1527 = distinct !DISubprogram(name: "__ubsan_handle_nullability_arg_abort", scope: !38, file: !38, line: 475, type: !1494, scopeLine: 475, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1528 = !DILocalVariable(name: "Data", arg: 1, scope: !1527, file: !38, line: 475, type: !1496)
!1529 = !DILocation(line: 475, column: 70, scope: !1527)
!1530 = !DILocation(line: 477, column: 20, scope: !1527)
!1531 = !DILocation(line: 477, column: 3, scope: !1527)
!1532 = !DILocation(line: 478, column: 1, scope: !1527)
!1533 = distinct !DISubprogram(name: "__ubsan_handle_pointer_overflow", scope: !38, file: !38, line: 494, type: !1534, scopeLine: 496, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1534 = !DISubroutineType(types: !1535)
!1535 = !{null, !1536, !798, !798}
!1536 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1537, size: 64)
!1537 = !DICompositeType(tag: DW_TAG_structure_type, name: "PointerOverflowData", file: !317, line: 101, size: 128, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS19PointerOverflowData")
!1538 = !DILocalVariable(name: "Data", arg: 1, scope: !1533, file: !38, line: 494, type: !1536)
!1539 = !DILocation(line: 494, column: 70, scope: !1533)
!1540 = !DILocalVariable(name: "Base", arg: 2, scope: !1533, file: !38, line: 495, type: !798)
!1541 = !DILocation(line: 495, column: 61, scope: !1533)
!1542 = !DILocalVariable(name: "Result", arg: 3, scope: !1533, file: !38, line: 496, type: !798)
!1543 = !DILocation(line: 496, column: 61, scope: !1533)
!1544 = !DILocation(line: 498, column: 29, scope: !1533)
!1545 = !DILocation(line: 498, column: 35, scope: !1533)
!1546 = !DILocation(line: 498, column: 41, scope: !1533)
!1547 = !DILocation(line: 498, column: 3, scope: !1533)
!1548 = !DILocation(line: 499, column: 1, scope: !1533)
!1549 = distinct !DISubprogram(name: "handlePointerOverflowImpl", linkageName: "_ZN7__ubsanL25handlePointerOverflowImplEP19PointerOverflowDatamm", scope: !224, file: !38, line: 480, type: !1534, scopeLine: 481, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1550 = !DILocalVariable(arg: 1, scope: !1549, file: !38, line: 480, type: !1536)
!1551 = !DILocation(line: 480, column: 69, scope: !1549)
!1552 = !DILocalVariable(name: "Base", arg: 2, scope: !1549, file: !38, line: 481, type: !798)
!1553 = !DILocation(line: 481, column: 51, scope: !1549)
!1554 = !DILocalVariable(name: "Result", arg: 3, scope: !1549, file: !38, line: 481, type: !798)
!1555 = !DILocation(line: 481, column: 69, scope: !1549)
!1556 = !DILocalVariable(name: "ET", scope: !1549, file: !38, line: 482, type: !256)
!1557 = !DILocation(line: 482, column: 13, scope: !1549)
!1558 = !DILocation(line: 483, column: 7, scope: !1559)
!1559 = distinct !DILexicalBlock(scope: !1549, file: !38, line: 483, column: 7)
!1560 = !DILocation(line: 483, column: 12, scope: !1559)
!1561 = !DILocation(line: 483, column: 17, scope: !1559)
!1562 = !DILocation(line: 484, column: 8, scope: !1559)
!1563 = !DILocation(line: 484, column: 5, scope: !1559)
!1564 = !DILocation(line: 485, column: 12, scope: !1565)
!1565 = distinct !DILexicalBlock(scope: !1559, file: !38, line: 485, column: 12)
!1566 = !DILocation(line: 485, column: 17, scope: !1565)
!1567 = !DILocation(line: 485, column: 22, scope: !1565)
!1568 = !DILocation(line: 486, column: 8, scope: !1565)
!1569 = !DILocation(line: 486, column: 5, scope: !1565)
!1570 = !DILocation(line: 487, column: 12, scope: !1571)
!1571 = distinct !DILexicalBlock(scope: !1565, file: !38, line: 487, column: 12)
!1572 = !DILocation(line: 487, column: 17, scope: !1571)
!1573 = !DILocation(line: 487, column: 22, scope: !1571)
!1574 = !DILocation(line: 488, column: 8, scope: !1571)
!1575 = !DILocation(line: 488, column: 5, scope: !1571)
!1576 = !DILocation(line: 490, column: 8, scope: !1571)
!1577 = !DILocation(line: 491, column: 21, scope: !1549)
!1578 = !DILocation(line: 491, column: 3, scope: !1549)
!1579 = distinct !DISubprogram(name: "__ubsan_handle_pointer_overflow_abort", scope: !38, file: !38, line: 501, type: !1534, scopeLine: 503, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1580 = !DILocalVariable(name: "Data", arg: 1, scope: !1579, file: !38, line: 501, type: !1536)
!1581 = !DILocation(line: 501, column: 76, scope: !1579)
!1582 = !DILocalVariable(name: "Base", arg: 2, scope: !1579, file: !38, line: 502, type: !798)
!1583 = !DILocation(line: 502, column: 67, scope: !1579)
!1584 = !DILocalVariable(name: "Result", arg: 3, scope: !1579, file: !38, line: 503, type: !798)
!1585 = !DILocation(line: 503, column: 67, scope: !1579)
!1586 = !DILocation(line: 505, column: 29, scope: !1579)
!1587 = !DILocation(line: 505, column: 35, scope: !1579)
!1588 = !DILocation(line: 505, column: 41, scope: !1579)
!1589 = !DILocation(line: 505, column: 3, scope: !1579)
!1590 = !DILocation(line: 506, column: 1, scope: !1579)
!1591 = distinct !DISubprogram(name: "__ubsan_handle_function_type_mismatch", scope: !38, file: !38, line: 516, type: !1592, scopeLine: 517, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1592 = !DISubroutineType(types: !1593)
!1593 = !{null, !1594, !798}
!1594 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1595, size: 64)
!1595 = !DICompositeType(tag: DW_TAG_structure_type, name: "FunctionTypeMismatchData", file: !317, line: 106, size: 192, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTS24FunctionTypeMismatchData")
!1596 = !DILocalVariable(name: "Data", arg: 1, scope: !1591, file: !38, line: 516, type: !1594)
!1597 = !DILocation(line: 516, column: 65, scope: !1591)
!1598 = !DILocalVariable(name: "Function", arg: 2, scope: !1591, file: !38, line: 517, type: !798)
!1599 = !DILocation(line: 517, column: 51, scope: !1591)
!1600 = !DILocation(line: 518, column: 30, scope: !1591)
!1601 = !DILocation(line: 518, column: 36, scope: !1591)
!1602 = !DILocation(line: 518, column: 3, scope: !1591)
!1603 = !DILocation(line: 519, column: 1, scope: !1591)
!1604 = distinct !DISubprogram(name: "handleFunctionTypeMismatch", linkageName: "_ZN7__ubsanL26handleFunctionTypeMismatchEP24FunctionTypeMismatchDatam", scope: !224, file: !38, line: 509, type: !1592, scopeLine: 510, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1605 = !DILocalVariable(arg: 1, scope: !1604, file: !38, line: 509, type: !1594)
!1606 = !DILocation(line: 509, column: 75, scope: !1604)
!1607 = !DILocalVariable(arg: 2, scope: !1604, file: !38, line: 510, type: !798)
!1608 = !DILocation(line: 510, column: 64, scope: !1604)
!1609 = !DILocalVariable(name: "ET", scope: !1604, file: !38, line: 511, type: !256)
!1610 = !DILocation(line: 511, column: 13, scope: !1604)
!1611 = !DILocation(line: 512, column: 21, scope: !1604)
!1612 = !DILocation(line: 512, column: 3, scope: !1604)
!1613 = distinct !DISubprogram(name: "__ubsan_handle_function_type_mismatch_abort", scope: !38, file: !38, line: 522, type: !1592, scopeLine: 523, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !218, retainedNodes: !334)
!1614 = !DILocalVariable(name: "Data", arg: 1, scope: !1613, file: !38, line: 522, type: !1594)
!1615 = !DILocation(line: 522, column: 71, scope: !1613)
!1616 = !DILocalVariable(name: "Function", arg: 2, scope: !1613, file: !38, line: 523, type: !798)
!1617 = !DILocation(line: 523, column: 57, scope: !1613)
!1618 = !DILocation(line: 524, column: 30, scope: !1613)
!1619 = !DILocation(line: 524, column: 36, scope: !1613)
!1620 = !DILocation(line: 524, column: 3, scope: !1613)
!1621 = !DILocation(line: 525, column: 1, scope: !1613)
!1622 = distinct !DISubprogram(name: "klee_overshift_check", scope: !201, file: !201, line: 20, type: !1623, scopeLine: 20, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !318, retainedNodes: !334)
!1623 = !DISubroutineType(types: !1624)
!1624 = !{null, !1625, !1625}
!1625 = !DIBasicType(name: "unsigned long long", size: 64, encoding: DW_ATE_unsigned)
!1626 = !DILocalVariable(name: "bitWidth", arg: 1, scope: !1622, file: !201, line: 20, type: !1625)
!1627 = !DILocation(line: 20, column: 46, scope: !1622)
!1628 = !DILocalVariable(name: "shift", arg: 2, scope: !1622, file: !201, line: 20, type: !1625)
!1629 = !DILocation(line: 20, column: 75, scope: !1622)
!1630 = !DILocation(line: 21, column: 7, scope: !1631)
!1631 = distinct !DILexicalBlock(scope: !1622, file: !201, line: 21, column: 7)
!1632 = !DILocation(line: 21, column: 16, scope: !1631)
!1633 = !DILocation(line: 21, column: 13, scope: !1631)
!1634 = !DILocation(line: 21, column: 7, scope: !1622)
!1635 = !DILocation(line: 27, column: 5, scope: !1636)
!1636 = distinct !DILexicalBlock(scope: !1631, file: !201, line: 21, column: 26)
!1637 = !DILocation(line: 29, column: 1, scope: !1622)
