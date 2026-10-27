; RUN: opt -passes=instcombine -print-pass-summary -pass-summary-compact -disable-output %s 2>&1 | FileCheck %s --check-prefix=COMPACT
; RUN: opt -passes=instcombine -print-pass-summary -pass-summary-name-width=10 -disable-output %s 2>&1 | FileCheck %s --check-prefix=WIDTH
; RUN: opt -passes=instcombine -print-pass-summary -pass-summary-max-ops=1 -disable-output %s 2>&1 | FileCheck %s --check-prefix=OPS
; RUN: opt -passes=instcombine -print-pass-summary -print-pass-summary-top=1 -disable-output %s 2>&1 | FileCheck %s --check-prefix=TOP

; COMPACT: [ps] InstCombine f: 2->2 | mul -1, shl +1{{$}}
; COMPACT: [ps] InstCombine g: 4->1 | add -3{{$}}

; WIDTH: [pass-summary] InstCombinePass on a_very_...: insts 2 -> 2, BBs 1 -> 1 | mul -1, shl +1{{$}}

; OPS: [pass-summary] InstCombinePass on f: insts 2 -> 2, BBs 1 -> 1 | mul -1, +1 more{{$}}

; Only the largest change (g) is printed, then the count of omitted lines.
; TOP-NOT: on f:
; TOP: [pass-summary] InstCombinePass on g: insts 4 -> 1, BBs 1 -> 1 | add -3
; TOP-NEXT: [pass-summary] top 1 of 3 lines shown, 2 omitted

define i32 @f(i32 %x) {
  %m = mul i32 %x, 8
  ret i32 %m
}

define i32 @g(i32 %x) {
  %a = add i32 %x, 0
  %b = add i32 %a, 0
  %c = add i32 %b, 0
  ret i32 %c
}

define i32 @a_very_long_function_name(i32 %x) {
  %m = mul i32 %x, 8
  ret i32 %m
}
