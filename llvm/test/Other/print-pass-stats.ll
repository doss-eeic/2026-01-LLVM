; RUN: opt -passes=instcombine -print-pass-stats -pass-stats-table -disable-output %s 2>&1 | FileCheck %s --check-prefix=TABLE
; RUN: opt -passes=instcombine -print-pass-stats -disable-output %s 2>&1 | FileCheck %s --check-prefix=CSV
; RUN: opt -passes=instcombine -disable-output %s 2>&1 | FileCheck %s --check-prefix=OFF --allow-empty
; RUN: opt -passes=instcombine -pass-stats-table -disable-output %s 2>&1 | FileCheck %s --check-prefix=OFF --allow-empty

; The times vary from run to run, so they are only matched by their shape.
; The row order of the table depends on the times, so rows use TABLE-DAG.
; TABLE: pass unit runs changed unchanged time_ms unch_ms unch%
; TABLE-DAG: InstCombinePass function 2 1 1 {{[0-9]+\.[0-9]}} {{[0-9]+\.[0-9]}} {{[0-9]+\.[0-9]}}
; TABLE-DAG: TOTAL {{[0-9]+}} {{[0-9]+}} {{[0-9]+}} {{[0-9]+\.[0-9]}} {{[0-9]+\.[0-9]}} {{[0-9]+\.[0-9]}}
; TABLE: note: 'changed' means the opcode counts
; TABLE: note: unch_ms is the time of runs counted as unchanged

; Without -pass-stats-table the CSV is printed. @g has 1 instruction (band 1),
; @f has 2 (band starting at 2).
; CSV: pass-stats,pass,unit,band_min_insts,runs,changed,
; CSV: pass-stats,"InstCombinePass",function,1,1,0,
; CSV: pass-stats,"InstCombinePass",function,2,1,1,
; CSV-NOT: unch_ms

; Without -print-pass-stats nothing is printed, even with -pass-stats-table.
; OFF-NOT: pass-stats
; OFF-NOT: unch_ms

define i32 @f(i32 %x) {
entry:
  %b = mul i32 %x, 2
  ret i32 %b
}

define i32 @g(i32 %x) {
entry:
  ret i32 %x
}
