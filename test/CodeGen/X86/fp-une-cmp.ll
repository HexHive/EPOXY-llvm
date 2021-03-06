; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=x86_64-unknown-unknown | FileCheck %s

; <rdar://problem/7859988>

; Make sure we don't generate more jumps than we need to. We used to generate
; something like this:
;
;       jne  LBB0_1
;       jnp  LBB0_2
;   LBB0_1:
;       jmp  LBB0_3
;   LBB0_2:
;       addsd ...
;   LBB0_3:
;
; Now we generate this:
;
;       jne  LBB0_2
;       jp   LBB0_2
;       addsd ...
;   LBB0_2:

define double @rdar_7859988(double %x, double %y) nounwind readnone optsize ssp {
; CHECK-LABEL: rdar_7859988:
; CHECK:       # BB#0: # %entry
; CHECK-NEXT:    mulsd %xmm1, %xmm0
; CHECK-NEXT:    xorpd %xmm1, %xmm1
; CHECK-NEXT:    ucomisd %xmm1, %xmm0
; CHECK-NEXT:    jne .LBB0_2
; CHECK-NEXT:    jp .LBB0_2
; CHECK-NEXT:  # BB#1: # %bb1
; CHECK-NEXT:    addsd {{.*}}(%rip), %xmm0
; CHECK-NEXT:  .LBB0_2: # %bb2
; CHECK-NEXT:    retq

entry:
  %mul = fmul double %x, %y
  %cmp = fcmp une double %mul, 0.000000e+00
  br i1 %cmp, label %bb2, label %bb1

bb1:
  %add = fadd double %mul, -1.000000e+00
  br label %bb2

bb2:
  %phi = phi double [ %add, %bb1 ], [ %mul, %entry ]
  ret double %phi
}

; FIXME: With branch weights indicated, bb2 should be placed ahead of bb1.

define double @profile_metadata(double %x, double %y) {
; CHECK-LABEL: profile_metadata:
; CHECK:       # BB#0: # %entry
; CHECK-NEXT:    mulsd %xmm1, %xmm0
; CHECK-NEXT:    xorpd %xmm1, %xmm1
; CHECK-NEXT:    ucomisd %xmm1, %xmm0
; CHECK-NEXT:    jne .LBB1_1
; CHECK-NEXT:    jnp .LBB1_2
; CHECK-NEXT:  .LBB1_1: # %bb1
; CHECK-NEXT:    addsd {{.*}}(%rip), %xmm0
; CHECK-NEXT:  .LBB1_2: # %bb2
; CHECK-NEXT:    retq

entry:
  %mul = fmul double %x, %y
  %cmp = fcmp une double %mul, 0.000000e+00
  br i1 %cmp, label %bb1, label %bb2, !prof !1

bb1:
  %add = fadd double %mul, -1.000000e+00
  br label %bb2

bb2:
  %phi = phi double [ %add, %bb1 ], [ %mul, %entry ]
  ret double %phi
}

!1 = !{!"branch_weights", i32 1, i32 1000}

