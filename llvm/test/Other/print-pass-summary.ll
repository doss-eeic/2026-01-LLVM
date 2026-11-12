; RUN: opt -passes=instcombine -print-pass-summary -disable-output %s 2>&1 | FileCheck %s
; RUN: opt -passes=instcombine -disable-output %s 2>&1 | FileCheck %s --check-prefix=OFF --allow-empty

; CHECK: [pass-summary] InstCombinePass on f: insts 2 -> 2, BBs 1 -> 1 | mul -1, shl +1
; OFF-NOT: pass-summary

define i32 @f(i32 %x) {
entry:
  %b = mul i32 %x, 2
  ret i32 %b
}
