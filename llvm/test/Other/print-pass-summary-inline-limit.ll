; RUN: opt -passes='cgscc(inline)' -print-pass-summary -disable-output %s 2>&1 | FileCheck %s

; Known limitation: the summary covers only the unit the pass runs on. The
; internal function @bar is deleted by the inliner after inlining, but it is
; outside the SCC (foo), so its instruction is not counted in this line.
; CHECK: [pass-summary] InlinerPass on (foo): insts 2 -> 1, BBs 1 -> 1 | call -1

define void @foo() {
entry:
  %call = call i32 @bar()
  ret void
}

define internal i32 @bar() {
entry:
  ret i32 42
}
