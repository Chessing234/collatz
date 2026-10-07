import Collatz.Exploration.ElevenHalvesArithmetic.Part04

namespace Collatz.Exploration.ElevenHalvesArithmetic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- Exact source residue and full affine trace for branch `001010010010101`. -/
theorem parameters_001010010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    : ∃ q : Nat, x0 = 1024*q+940 ∧ x1 = 512*q+470 ∧ x2 = 256*q+235 ∧ x3 = 768*q+706 ∧ x4 = 384*q+353 ∧ x5 = 1152*q+1060 ∧ x6 = 576*q+530 ∧ x7 = 288*q+265 ∧ x8 = 864*q+796 ∧ x9 = 432*q+398 ∧ x10 = 216*q+199 ∧ x11 = 648*q+598 ∧ x12 = 324*q+299 ∧ x13 = 972*q+898 ∧ x14 = 486*q+449 ∧ x15 = 1458*q+1348 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_00101001001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `001010010100100`. -/
theorem parameters_001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    : ∃ q : Nat, x0 = 1024*q+492 ∧ x1 = 512*q+246 ∧ x2 = 256*q+123 ∧ x3 = 768*q+370 ∧ x4 = 384*q+185 ∧ x5 = 1152*q+556 ∧ x6 = 576*q+278 ∧ x7 = 288*q+139 ∧ x8 = 864*q+418 ∧ x9 = 432*q+209 ∧ x10 = 1296*q+628 ∧ x11 = 648*q+314 ∧ x12 = 324*q+157 ∧ x13 = 972*q+472 ∧ x14 = 486*q+236 ∧ x15 = 243*q+118 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_00101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `001010010100101`. -/
theorem parameters_001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    : ∃ q : Nat, x0 = 1024*q+1004 ∧ x1 = 512*q+502 ∧ x2 = 256*q+251 ∧ x3 = 768*q+754 ∧ x4 = 384*q+377 ∧ x5 = 1152*q+1132 ∧ x6 = 576*q+566 ∧ x7 = 288*q+283 ∧ x8 = 864*q+850 ∧ x9 = 432*q+425 ∧ x10 = 1296*q+1276 ∧ x11 = 648*q+638 ∧ x12 = 324*q+319 ∧ x13 = 972*q+958 ∧ x14 = 486*q+479 ∧ x15 = 1458*q+1438 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_00101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `010010010100100`. -/
theorem parameters_010010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    : ∃ q : Nat, x0 = 1024*q+834 ∧ x1 = 512*q+417 ∧ x2 = 1536*q+1252 ∧ x3 = 768*q+626 ∧ x4 = 384*q+313 ∧ x5 = 1152*q+940 ∧ x6 = 576*q+470 ∧ x7 = 288*q+235 ∧ x8 = 864*q+706 ∧ x9 = 432*q+353 ∧ x10 = 1296*q+1060 ∧ x11 = 648*q+530 ∧ x12 = 324*q+265 ∧ x13 = 972*q+796 ∧ x14 = 486*q+398 ∧ x15 = 243*q+199 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_01001001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `010010010100101`. -/
theorem parameters_010010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    : ∃ q : Nat, x0 = 1024*q+322 ∧ x1 = 512*q+161 ∧ x2 = 1536*q+484 ∧ x3 = 768*q+242 ∧ x4 = 384*q+121 ∧ x5 = 1152*q+364 ∧ x6 = 576*q+182 ∧ x7 = 288*q+91 ∧ x8 = 864*q+274 ∧ x9 = 432*q+137 ∧ x10 = 1296*q+412 ∧ x11 = 648*q+206 ∧ x12 = 324*q+103 ∧ x13 = 972*q+310 ∧ x14 = 486*q+155 ∧ x15 = 1458*q+466 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_01001001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `010010100100100`. -/
theorem parameters_010010100100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    : ∃ q : Nat, x0 = 1024*q+114 ∧ x1 = 512*q+57 ∧ x2 = 1536*q+172 ∧ x3 = 768*q+86 ∧ x4 = 384*q+43 ∧ x5 = 1152*q+130 ∧ x6 = 576*q+65 ∧ x7 = 1728*q+196 ∧ x8 = 864*q+98 ∧ x9 = 432*q+49 ∧ x10 = 1296*q+148 ∧ x11 = 648*q+74 ∧ x12 = 324*q+37 ∧ x13 = 972*q+112 ∧ x14 = 486*q+56 ∧ x15 = 243*q+28 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_01001010010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `010010100100101`. -/
theorem parameters_010010100100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    : ∃ q : Nat, x0 = 1024*q+626 ∧ x1 = 512*q+313 ∧ x2 = 1536*q+940 ∧ x3 = 768*q+470 ∧ x4 = 384*q+235 ∧ x5 = 1152*q+706 ∧ x6 = 576*q+353 ∧ x7 = 1728*q+1060 ∧ x8 = 864*q+530 ∧ x9 = 432*q+265 ∧ x10 = 1296*q+796 ∧ x11 = 648*q+398 ∧ x12 = 324*q+199 ∧ x13 = 972*q+598 ∧ x14 = 486*q+299 ∧ x15 = 1458*q+898 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_01001010010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `010010100101000`. -/
theorem parameters_010010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    : ∃ q : Nat, x0 = 1024*q+498 ∧ x1 = 512*q+249 ∧ x2 = 1536*q+748 ∧ x3 = 768*q+374 ∧ x4 = 384*q+187 ∧ x5 = 1152*q+562 ∧ x6 = 576*q+281 ∧ x7 = 1728*q+844 ∧ x8 = 864*q+422 ∧ x9 = 432*q+211 ∧ x10 = 1296*q+634 ∧ x11 = 648*q+317 ∧ x12 = 1944*q+952 ∧ x13 = 972*q+476 ∧ x14 = 486*q+238 ∧ x15 = 243*q+119 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_01001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `010010100101001`. -/
theorem parameters_010010100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    : ∃ q : Nat, x0 = 1024*q+1010 ∧ x1 = 512*q+505 ∧ x2 = 1536*q+1516 ∧ x3 = 768*q+758 ∧ x4 = 384*q+379 ∧ x5 = 1152*q+1138 ∧ x6 = 576*q+569 ∧ x7 = 1728*q+1708 ∧ x8 = 864*q+854 ∧ x9 = 432*q+427 ∧ x10 = 1296*q+1282 ∧ x11 = 648*q+641 ∧ x12 = 1944*q+1924 ∧ x13 = 972*q+962 ∧ x14 = 486*q+481 ∧ x15 = 1458*q+1444 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_01001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `010100100101000`. -/
theorem parameters_010100100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    : ∃ q : Nat, x0 = 1024*q+726 ∧ x1 = 512*q+363 ∧ x2 = 1536*q+1090 ∧ x3 = 768*q+545 ∧ x4 = 2304*q+1636 ∧ x5 = 1152*q+818 ∧ x6 = 576*q+409 ∧ x7 = 1728*q+1228 ∧ x8 = 864*q+614 ∧ x9 = 432*q+307 ∧ x10 = 1296*q+922 ∧ x11 = 648*q+461 ∧ x12 = 1944*q+1384 ∧ x13 = 972*q+692 ∧ x14 = 486*q+346 ∧ x15 = 243*q+173 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_01010010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `010100100101001`. -/
theorem parameters_010100100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    : ∃ q : Nat, x0 = 1024*q+214 ∧ x1 = 512*q+107 ∧ x2 = 1536*q+322 ∧ x3 = 768*q+161 ∧ x4 = 2304*q+484 ∧ x5 = 1152*q+242 ∧ x6 = 576*q+121 ∧ x7 = 1728*q+364 ∧ x8 = 864*q+182 ∧ x9 = 432*q+91 ∧ x10 = 1296*q+274 ∧ x11 = 648*q+137 ∧ x12 = 1944*q+412 ∧ x13 = 972*q+206 ∧ x14 = 486*q+103 ∧ x15 = 1458*q+310 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_01010010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `010100101001000`. -/
theorem parameters_010100101001000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    : ∃ q : Nat, x0 = 1024*q+246 ∧ x1 = 512*q+123 ∧ x2 = 1536*q+370 ∧ x3 = 768*q+185 ∧ x4 = 2304*q+556 ∧ x5 = 1152*q+278 ∧ x6 = 576*q+139 ∧ x7 = 1728*q+418 ∧ x8 = 864*q+209 ∧ x9 = 2592*q+628 ∧ x10 = 1296*q+314 ∧ x11 = 648*q+157 ∧ x12 = 1944*q+472 ∧ x13 = 972*q+236 ∧ x14 = 486*q+118 ∧ x15 = 243*q+59 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_01010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `010100101001001`. -/
theorem parameters_010100101001001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    : ∃ q : Nat, x0 = 1024*q+758 ∧ x1 = 512*q+379 ∧ x2 = 1536*q+1138 ∧ x3 = 768*q+569 ∧ x4 = 2304*q+1708 ∧ x5 = 1152*q+854 ∧ x6 = 576*q+427 ∧ x7 = 1728*q+1282 ∧ x8 = 864*q+641 ∧ x9 = 2592*q+1924 ∧ x10 = 1296*q+962 ∧ x11 = 648*q+481 ∧ x12 = 1944*q+1444 ∧ x13 = 972*q+722 ∧ x14 = 486*q+361 ∧ x15 = 1458*q+1084 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_01010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `100100101001010`. -/
theorem parameters_100100101001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    : ∃ q : Nat, x0 = 512*q+161 ∧ x1 = 1536*q+484 ∧ x2 = 768*q+242 ∧ x3 = 384*q+121 ∧ x4 = 1152*q+364 ∧ x5 = 576*q+182 ∧ x6 = 288*q+91 ∧ x7 = 864*q+274 ∧ x8 = 432*q+137 ∧ x9 = 1296*q+412 ∧ x10 = 648*q+206 ∧ x11 = 324*q+103 ∧ x12 = 972*q+310 ∧ x13 = 486*q+155 ∧ x14 = 1458*q+466 ∧ x15 = 729*q+233 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_10010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `100101001001010`. -/
theorem parameters_100101001001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    : ∃ q : Nat, x0 = 512*q+313 ∧ x1 = 1536*q+940 ∧ x2 = 768*q+470 ∧ x3 = 384*q+235 ∧ x4 = 1152*q+706 ∧ x5 = 576*q+353 ∧ x6 = 1728*q+1060 ∧ x7 = 864*q+530 ∧ x8 = 432*q+265 ∧ x9 = 1296*q+796 ∧ x10 = 648*q+398 ∧ x11 = 324*q+199 ∧ x12 = 972*q+598 ∧ x13 = 486*q+299 ∧ x14 = 1458*q+898 ∧ x15 = 729*q+449 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_10010100100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `100101001010010`. -/
theorem parameters_100101001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    : ∃ q : Nat, x0 = 512*q+505 ∧ x1 = 1536*q+1516 ∧ x2 = 768*q+758 ∧ x3 = 384*q+379 ∧ x4 = 1152*q+1138 ∧ x5 = 576*q+569 ∧ x6 = 1728*q+1708 ∧ x7 = 864*q+854 ∧ x8 = 432*q+427 ∧ x9 = 1296*q+1282 ∧ x10 = 648*q+641 ∧ x11 = 1944*q+1924 ∧ x12 = 972*q+962 ∧ x13 = 486*q+481 ∧ x14 = 1458*q+1444 ∧ x15 = 729*q+722 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_10010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `101001001010010`. -/
theorem parameters_101001001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    : ∃ q : Nat, x0 = 512*q+107 ∧ x1 = 1536*q+322 ∧ x2 = 768*q+161 ∧ x3 = 2304*q+484 ∧ x4 = 1152*q+242 ∧ x5 = 576*q+121 ∧ x6 = 1728*q+364 ∧ x7 = 864*q+182 ∧ x8 = 432*q+91 ∧ x9 = 1296*q+274 ∧ x10 = 648*q+137 ∧ x11 = 1944*q+412 ∧ x12 = 972*q+206 ∧ x13 = 486*q+103 ∧ x14 = 1458*q+310 ∧ x15 = 729*q+155 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_10100100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `101001010010010`. -/
theorem parameters_101001010010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    : ∃ q : Nat, x0 = 512*q+379 ∧ x1 = 1536*q+1138 ∧ x2 = 768*q+569 ∧ x3 = 2304*q+1708 ∧ x4 = 1152*q+854 ∧ x5 = 576*q+427 ∧ x6 = 1728*q+1282 ∧ x7 = 864*q+641 ∧ x8 = 2592*q+1924 ∧ x9 = 1296*q+962 ∧ x10 = 648*q+481 ∧ x11 = 1944*q+1444 ∧ x12 = 972*q+722 ∧ x13 = 486*q+361 ∧ x14 = 1458*q+1084 ∧ x15 = 729*q+542 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_10100101001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hstep := r14.1
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    omega

/-- Exact source residue and full affine trace for branch `0010010100101000`. -/
theorem parameters_0010010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    : ∃ q : Nat, x0 = 2048*q+996 ∧ x1 = 1024*q+498 ∧ x2 = 512*q+249 ∧ x3 = 1536*q+748 ∧ x4 = 768*q+374 ∧ x5 = 384*q+187 ∧ x6 = 1152*q+562 ∧ x7 = 576*q+281 ∧ x8 = 1728*q+844 ∧ x9 = 864*q+422 ∧ x10 = 432*q+211 ∧ x11 = 1296*q+634 ∧ x12 = 648*q+317 ∧ x13 = 1944*q+952 ∧ x14 = 972*q+476 ∧ x15 = 486*q+238 ∧ x16 = 243*q+119 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hstep := r15.1
  have hparity := r15.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega

/-- Exact source residue and full affine trace for branch `0010010100101001`. -/
theorem parameters_0010010100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    : ∃ q : Nat, x0 = 2048*q+2020 ∧ x1 = 1024*q+1010 ∧ x2 = 512*q+505 ∧ x3 = 1536*q+1516 ∧ x4 = 768*q+758 ∧ x5 = 384*q+379 ∧ x6 = 1152*q+1138 ∧ x7 = 576*q+569 ∧ x8 = 1728*q+1708 ∧ x9 = 864*q+854 ∧ x10 = 432*q+427 ∧ x11 = 1296*q+1282 ∧ x12 = 648*q+641 ∧ x13 = 1944*q+1924 ∧ x14 = 972*q+962 ∧ x15 = 486*q+481 ∧ x16 = 1458*q+1444 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hstep := r15.1
  have hparity := r15.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega

/-- Exact source residue and full affine trace for branch `0010100100101000`. -/
theorem parameters_0010100100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    : ∃ q : Nat, x0 = 2048*q+1452 ∧ x1 = 1024*q+726 ∧ x2 = 512*q+363 ∧ x3 = 1536*q+1090 ∧ x4 = 768*q+545 ∧ x5 = 2304*q+1636 ∧ x6 = 1152*q+818 ∧ x7 = 576*q+409 ∧ x8 = 1728*q+1228 ∧ x9 = 864*q+614 ∧ x10 = 432*q+307 ∧ x11 = 1296*q+922 ∧ x12 = 648*q+461 ∧ x13 = 1944*q+1384 ∧ x14 = 972*q+692 ∧ x15 = 486*q+346 ∧ x16 = 243*q+173 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_001010010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hstep := r15.1
  have hparity := r15.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega

/-- Exact source residue and full affine trace for branch `0010100100101001`. -/
theorem parameters_0010100100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    : ∃ q : Nat, x0 = 2048*q+428 ∧ x1 = 1024*q+214 ∧ x2 = 512*q+107 ∧ x3 = 1536*q+322 ∧ x4 = 768*q+161 ∧ x5 = 2304*q+484 ∧ x6 = 1152*q+242 ∧ x7 = 576*q+121 ∧ x8 = 1728*q+364 ∧ x9 = 864*q+182 ∧ x10 = 432*q+91 ∧ x11 = 1296*q+274 ∧ x12 = 648*q+137 ∧ x13 = 1944*q+412 ∧ x14 = 972*q+206 ∧ x15 = 486*q+103 ∧ x16 = 1458*q+310 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_001010010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hstep := r15.1
  have hparity := r15.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega

/-- Exact source residue and full affine trace for branch `0010100101001000`. -/
theorem parameters_0010100101001000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    : ∃ q : Nat, x0 = 2048*q+492 ∧ x1 = 1024*q+246 ∧ x2 = 512*q+123 ∧ x3 = 1536*q+370 ∧ x4 = 768*q+185 ∧ x5 = 2304*q+556 ∧ x6 = 1152*q+278 ∧ x7 = 576*q+139 ∧ x8 = 1728*q+418 ∧ x9 = 864*q+209 ∧ x10 = 2592*q+628 ∧ x11 = 1296*q+314 ∧ x12 = 648*q+157 ∧ x13 = 1944*q+472 ∧ x14 = 972*q+236 ∧ x15 = 486*q+118 ∧ x16 = 243*q+59 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hstep := r15.1
  have hparity := r15.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega

/-- Exact source residue and full affine trace for branch `0010100101001001`. -/
theorem parameters_0010100101001001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    : ∃ q : Nat, x0 = 2048*q+1516 ∧ x1 = 1024*q+758 ∧ x2 = 512*q+379 ∧ x3 = 1536*q+1138 ∧ x4 = 768*q+569 ∧ x5 = 2304*q+1708 ∧ x6 = 1152*q+854 ∧ x7 = 576*q+427 ∧ x8 = 1728*q+1282 ∧ x9 = 864*q+641 ∧ x10 = 2592*q+1924 ∧ x11 = 1296*q+962 ∧ x12 = 648*q+481 ∧ x13 = 1944*q+1444 ∧ x14 = 972*q+722 ∧ x15 = 486*q+361 ∧ x16 = 1458*q+1084 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hstep := r15.1
  have hparity := r15.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega

/-- Exact source residue and full affine trace for branch `0100100101001010`. -/
theorem parameters_0100100101001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    : ∃ q : Nat, x0 = 1024*q+322 ∧ x1 = 512*q+161 ∧ x2 = 1536*q+484 ∧ x3 = 768*q+242 ∧ x4 = 384*q+121 ∧ x5 = 1152*q+364 ∧ x6 = 576*q+182 ∧ x7 = 288*q+91 ∧ x8 = 864*q+274 ∧ x9 = 432*q+137 ∧ x10 = 1296*q+412 ∧ x11 = 648*q+206 ∧ x12 = 324*q+103 ∧ x13 = 972*q+310 ∧ x14 = 486*q+155 ∧ x15 = 1458*q+466 ∧ x16 = 729*q+233 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_010010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hstep := r15.1
  have hparity := r15.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · exact p15
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega

/-- Exact source residue and full affine trace for branch `0100101001001010`. -/
theorem parameters_0100101001001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    : ∃ q : Nat, x0 = 1024*q+626 ∧ x1 = 512*q+313 ∧ x2 = 1536*q+940 ∧ x3 = 768*q+470 ∧ x4 = 384*q+235 ∧ x5 = 1152*q+706 ∧ x6 = 576*q+353 ∧ x7 = 1728*q+1060 ∧ x8 = 864*q+530 ∧ x9 = 432*q+265 ∧ x10 = 1296*q+796 ∧ x11 = 648*q+398 ∧ x12 = 324*q+199 ∧ x13 = 972*q+598 ∧ x14 = 486*q+299 ∧ x15 = 1458*q+898 ∧ x16 = 729*q+449 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_010010100100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hstep := r15.1
  have hparity := r15.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · exact p15
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14
    omega


end Collatz.Exploration.ElevenHalvesArithmetic
