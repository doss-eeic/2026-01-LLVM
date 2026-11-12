; RUN: opt -passes=instcombine -print-pass-stats -pass-stats-text-hash -pass-stats-table -disable-output %s 2>&1 | FileCheck %s
; RUN: opt -passes=instcombine -print-pass-stats -pass-stats-table -disable-output %s 2>&1 | FileCheck %s --check-prefix=NOHASH

; InstCombine moves the constant to the right: add i32 1, %x -> add i32 %x, 1.
; The opcode counts do not change, so only the text check sees the change.
; CHECK: pass{{ +}}unit{{.*}}unch%{{ +}}chg_detail{{ +}}chg_text{{ +}}missed{{ +}}miss%
; CHECK: InstCombinePass{{.*}} 1{{ +}}1{{ +}}100.0{{$}}
; CHECK: note: chg_detail and chg_text

; NOHASH-NOT: chg_detail

define i32 @f(i32 %x) {
  %r = add i32 1, %x
  ret i32 %r
}
