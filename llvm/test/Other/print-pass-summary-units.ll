; RUN: opt -passes='loop(loop-instsimplify)' -print-pass-summary -disable-output %s 2>&1 | FileCheck %s --check-prefix=LOOP
; RUN: opt -passes='cgscc(inline)' -print-pass-summary -disable-output %s 2>&1 | FileCheck %s --check-prefix=SCC
; RUN: opt -passes='loop(loop-deletion)' -print-pass-summary -disable-output %s 2>&1 | FileCheck %s --check-prefix=DEL

; Loop passes report the size of the whole parent function, because they can
; also change blocks outside the loop (preheader, exit blocks, LCSSA phis).
; LOOP: [pass-summary] LoopInstSimplifyPass on loop %loop in with_loop: insts 8 -> 7, BBs 3 -> 3 | add -1
; SCC: [pass-summary] InlinerPass on (caller): insts 2 -> 2, BBs 1 -> 1 | add +1, call -1
; A deleted loop invalidates the loop, but its summary line is still printed.
; DEL: [pass-summary] LoopDeletionPass on loop %loop in dead_loop: insts 6 -> 2, BBs 3 -> 2

define i32 @with_loop(i32 %n) {
entry:
  br label %loop
loop:
  %i = phi i32 [ 0, %entry ], [ %i.next, %loop ]
  %z = add i32 %i, 0
  %i.next = add i32 %z, 1
  %c = icmp slt i32 %i.next, %n
  br i1 %c, label %loop, label %exit
exit:
  ret i32 %i.next
}

define void @dead_loop(i32 %n) mustprogress {
entry:
  br label %loop
loop:
  %i = phi i32 [ 0, %entry ], [ %i.next, %loop ]
  %i.next = add nuw nsw i32 %i, 1
  %c = icmp slt i32 %i.next, %n
  br i1 %c, label %loop, label %exit
exit:
  ret void
}

define internal i32 @callee(i32 %x) {
  %r = add i32 %x, 1
  ret i32 %r
}

define i32 @caller(i32 %y) {
  %c = call i32 @callee(i32 %y)
  ret i32 %c
}
