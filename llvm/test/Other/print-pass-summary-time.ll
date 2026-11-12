; RUN: opt -passes=instcombine -print-pass-summary -print-pass-summary-time -disable-output %s 2>&1 | FileCheck %s --check-prefix=TIME
; RUN: opt -passes=instcombine -print-pass-summary -disable-output %s 2>&1 | FileCheck %s --check-prefix=NOTIME

; With -print-pass-summary-time the elapsed time is appended. Passes that did
; not change the IR (@g) are still skipped unless a minimum time is given.
; TIME: [pass-summary] InstCombinePass on f: insts 2 -> 2, BBs 1 -> 1 | mul -1, shl +1 | time={{[0-9]+}}us
; TIME-NOT: on g

; Without the option the output is unchanged.
; NOTIME: [pass-summary] InstCombinePass on f: insts 2 -> 2, BBs 1 -> 1 | mul -1, shl +1{{$}}

define i32 @f(i32 %x) {
entry:
  %b = mul i32 %x, 2
  ret i32 %b
}

define i32 @g(i32 %x) {
entry:
  ret i32 %x
}
