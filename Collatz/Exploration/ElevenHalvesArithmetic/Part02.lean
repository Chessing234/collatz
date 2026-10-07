import Collatz.Exploration.ElevenHalvesArithmetic.Part01

namespace Collatz.Exploration.ElevenHalvesArithmetic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- Exact source residue and full affine trace for branch `0101001010`. -/
theorem parameters_0101001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
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
    : ∃ q : Nat, x0 = 64*q+54 ∧ x1 = 32*q+27 ∧ x2 = 96*q+82 ∧ x3 = 48*q+41 ∧ x4 = 144*q+124 ∧ x5 = 72*q+62 ∧ x6 = 36*q+31 ∧ x7 = 108*q+94 ∧ x8 = 54*q+47 ∧ x9 = 162*q+142 ∧ x10 = 81*q+71 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hstep := r9.1
  have hparity := r9.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8
    omega

/-- Exact source residue and full affine trace for branch `1001001010`. -/
theorem parameters_1001001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
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
    : ∃ q : Nat, x0 = 64*q+33 ∧ x1 = 192*q+100 ∧ x2 = 96*q+50 ∧ x3 = 48*q+25 ∧ x4 = 144*q+76 ∧ x5 = 72*q+38 ∧ x6 = 36*q+19 ∧ x7 = 108*q+58 ∧ x8 = 54*q+29 ∧ x9 = 162*q+88 ∧ x10 = 81*q+44 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_100100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hstep := r9.1
  have hparity := r9.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8
    omega

/-- Exact source residue and full affine trace for branch `1001010010`. -/
theorem parameters_1001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
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
    : ∃ q : Nat, x0 = 64*q+57 ∧ x1 = 192*q+172 ∧ x2 = 96*q+86 ∧ x3 = 48*q+43 ∧ x4 = 144*q+130 ∧ x5 = 72*q+65 ∧ x6 = 216*q+196 ∧ x7 = 108*q+98 ∧ x8 = 54*q+49 ∧ x9 = 162*q+148 ∧ x10 = 81*q+74 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hstep := r9.1
  have hparity := r9.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8
    omega

/-- Exact source residue and full affine trace for branch `1010010010`. -/
theorem parameters_1010010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
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
    : ∃ q : Nat, x0 = 64*q+43 ∧ x1 = 192*q+130 ∧ x2 = 96*q+65 ∧ x3 = 288*q+196 ∧ x4 = 144*q+98 ∧ x5 = 72*q+49 ∧ x6 = 216*q+148 ∧ x7 = 108*q+74 ∧ x8 = 54*q+37 ∧ x9 = 162*q+112 ∧ x10 = 81*q+56 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_101001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hstep := r9.1
  have hparity := r9.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8
    omega

/-- Exact source residue and full affine trace for branch `1010010100`. -/
theorem parameters_1010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
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
    : ∃ q : Nat, x0 = 64*q+59 ∧ x1 = 192*q+178 ∧ x2 = 96*q+89 ∧ x3 = 288*q+268 ∧ x4 = 144*q+134 ∧ x5 = 72*q+67 ∧ x6 = 216*q+202 ∧ x7 = 108*q+101 ∧ x8 = 324*q+304 ∧ x9 = 162*q+152 ∧ x10 = 81*q+76 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hstep := r9.1
  have hparity := r9.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8
    omega

/-- Exact source residue and full affine trace for branch `1010010101`. -/
theorem parameters_1010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    : ∃ q : Nat, x0 = 64*q+27 ∧ x1 = 192*q+82 ∧ x2 = 96*q+41 ∧ x3 = 288*q+124 ∧ x4 = 144*q+62 ∧ x5 = 72*q+31 ∧ x6 = 216*q+94 ∧ x7 = 108*q+47 ∧ x8 = 324*q+142 ∧ x9 = 162*q+71 ∧ x10 = 486*q+214 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hstep := r9.1
  have hparity := r9.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8
    omega

/-- Exact source residue and full affine trace for branch `00100101000`. -/
theorem parameters_00100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    : ∃ q : Nat, x0 = 256*q+100 ∧ x1 = 128*q+50 ∧ x2 = 64*q+25 ∧ x3 = 192*q+76 ∧ x4 = 96*q+38 ∧ x5 = 48*q+19 ∧ x6 = 144*q+58 ∧ x7 = 72*q+29 ∧ x8 = 216*q+88 ∧ x9 = 108*q+44 ∧ x10 = 54*q+22 ∧ x11 = 27*q+11 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `00100101001`. -/
theorem parameters_00100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    : ∃ q : Nat, x0 = 256*q+228 ∧ x1 = 128*q+114 ∧ x2 = 64*q+57 ∧ x3 = 192*q+172 ∧ x4 = 96*q+86 ∧ x5 = 48*q+43 ∧ x6 = 144*q+130 ∧ x7 = 72*q+65 ∧ x8 = 216*q+196 ∧ x9 = 108*q+98 ∧ x10 = 54*q+49 ∧ x11 = 162*q+148 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `00101001000`. -/
theorem parameters_00101001000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    : ∃ q : Nat, x0 = 256*q+44 ∧ x1 = 128*q+22 ∧ x2 = 64*q+11 ∧ x3 = 192*q+34 ∧ x4 = 96*q+17 ∧ x5 = 288*q+52 ∧ x6 = 144*q+26 ∧ x7 = 72*q+13 ∧ x8 = 216*q+40 ∧ x9 = 108*q+20 ∧ x10 = 54*q+10 ∧ x11 = 27*q+5 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `00101001001`. -/
theorem parameters_00101001001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    : ∃ q : Nat, x0 = 256*q+172 ∧ x1 = 128*q+86 ∧ x2 = 64*q+43 ∧ x3 = 192*q+130 ∧ x4 = 96*q+65 ∧ x5 = 288*q+196 ∧ x6 = 144*q+98 ∧ x7 = 72*q+49 ∧ x8 = 216*q+148 ∧ x9 = 108*q+74 ∧ x10 = 54*q+37 ∧ x11 = 162*q+112 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `00101001010`. -/
theorem parameters_00101001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+108 ∧ x1 = 64*q+54 ∧ x2 = 32*q+27 ∧ x3 = 96*q+82 ∧ x4 = 48*q+41 ∧ x5 = 144*q+124 ∧ x6 = 72*q+62 ∧ x7 = 36*q+31 ∧ x8 = 108*q+94 ∧ x9 = 54*q+47 ∧ x10 = 162*q+142 ∧ x11 = 81*q+71 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `01001001010`. -/
theorem parameters_01001001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+66 ∧ x1 = 64*q+33 ∧ x2 = 192*q+100 ∧ x3 = 96*q+50 ∧ x4 = 48*q+25 ∧ x5 = 144*q+76 ∧ x6 = 72*q+38 ∧ x7 = 36*q+19 ∧ x8 = 108*q+58 ∧ x9 = 54*q+29 ∧ x10 = 162*q+88 ∧ x11 = 81*q+44 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0100100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `01001010010`. -/
theorem parameters_01001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+114 ∧ x1 = 64*q+57 ∧ x2 = 192*q+172 ∧ x3 = 96*q+86 ∧ x4 = 48*q+43 ∧ x5 = 144*q+130 ∧ x6 = 72*q+65 ∧ x7 = 216*q+196 ∧ x8 = 108*q+98 ∧ x9 = 54*q+49 ∧ x10 = 162*q+148 ∧ x11 = 81*q+74 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `01010010010`. -/
theorem parameters_01010010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+86 ∧ x1 = 64*q+43 ∧ x2 = 192*q+130 ∧ x3 = 96*q+65 ∧ x4 = 288*q+196 ∧ x5 = 144*q+98 ∧ x6 = 72*q+49 ∧ x7 = 216*q+148 ∧ x8 = 108*q+74 ∧ x9 = 54*q+37 ∧ x10 = 162*q+112 ∧ x11 = 81*q+56 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0101001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `01010010100`. -/
theorem parameters_01010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+118 ∧ x1 = 64*q+59 ∧ x2 = 192*q+178 ∧ x3 = 96*q+89 ∧ x4 = 288*q+268 ∧ x5 = 144*q+134 ∧ x6 = 72*q+67 ∧ x7 = 216*q+202 ∧ x8 = 108*q+101 ∧ x9 = 324*q+304 ∧ x10 = 162*q+152 ∧ x11 = 81*q+76 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `01010010101`. -/
theorem parameters_01010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    : ∃ q : Nat, x0 = 128*q+54 ∧ x1 = 64*q+27 ∧ x2 = 192*q+82 ∧ x3 = 96*q+41 ∧ x4 = 288*q+124 ∧ x5 = 144*q+62 ∧ x6 = 72*q+31 ∧ x7 = 216*q+94 ∧ x8 = 108*q+47 ∧ x9 = 324*q+142 ∧ x10 = 162*q+71 ∧ x11 = 486*q+214 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `10010010100`. -/
theorem parameters_10010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+33 ∧ x1 = 384*q+100 ∧ x2 = 192*q+50 ∧ x3 = 96*q+25 ∧ x4 = 288*q+76 ∧ x5 = 144*q+38 ∧ x6 = 72*q+19 ∧ x7 = 216*q+58 ∧ x8 = 108*q+29 ∧ x9 = 324*q+88 ∧ x10 = 162*q+44 ∧ x11 = 81*q+22 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_1001001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `10010010101`. -/
theorem parameters_10010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    : ∃ q : Nat, x0 = 128*q+97 ∧ x1 = 384*q+292 ∧ x2 = 192*q+146 ∧ x3 = 96*q+73 ∧ x4 = 288*q+220 ∧ x5 = 144*q+110 ∧ x6 = 72*q+55 ∧ x7 = 216*q+166 ∧ x8 = 108*q+83 ∧ x9 = 324*q+250 ∧ x10 = 162*q+125 ∧ x11 = 486*q+376 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_1001001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `10010100100`. -/
theorem parameters_10010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+57 ∧ x1 = 384*q+172 ∧ x2 = 192*q+86 ∧ x3 = 96*q+43 ∧ x4 = 288*q+130 ∧ x5 = 144*q+65 ∧ x6 = 432*q+196 ∧ x7 = 216*q+98 ∧ x8 = 108*q+49 ∧ x9 = 324*q+148 ∧ x10 = 162*q+74 ∧ x11 = 81*q+37 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_1001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `10010100101`. -/
theorem parameters_10010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+121 ∧ x1 = 384*q+364 ∧ x2 = 192*q+182 ∧ x3 = 96*q+91 ∧ x4 = 288*q+274 ∧ x5 = 144*q+137 ∧ x6 = 432*q+412 ∧ x7 = 216*q+206 ∧ x8 = 108*q+103 ∧ x9 = 324*q+310 ∧ x10 = 162*q+155 ∧ x11 = 486*q+466 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_1001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `10100100100`. -/
theorem parameters_10100100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    : ∃ q : Nat, x0 = 128*q+43 ∧ x1 = 384*q+130 ∧ x2 = 192*q+65 ∧ x3 = 576*q+196 ∧ x4 = 288*q+98 ∧ x5 = 144*q+49 ∧ x6 = 432*q+148 ∧ x7 = 216*q+74 ∧ x8 = 108*q+37 ∧ x9 = 324*q+112 ∧ x10 = 162*q+56 ∧ x11 = 81*q+28 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_1010010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `10100100101`. -/
theorem parameters_10100100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+107 ∧ x1 = 384*q+322 ∧ x2 = 192*q+161 ∧ x3 = 576*q+484 ∧ x4 = 288*q+242 ∧ x5 = 144*q+121 ∧ x6 = 432*q+364 ∧ x7 = 216*q+182 ∧ x8 = 108*q+91 ∧ x9 = 324*q+274 ∧ x10 = 162*q+137 ∧ x11 = 486*q+412 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_1010010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `10100101000`. -/
theorem parameters_10100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    : ∃ q : Nat, x0 = 128*q+59 ∧ x1 = 384*q+178 ∧ x2 = 192*q+89 ∧ x3 = 576*q+268 ∧ x4 = 288*q+134 ∧ x5 = 144*q+67 ∧ x6 = 432*q+202 ∧ x7 = 216*q+101 ∧ x8 = 648*q+304 ∧ x9 = 324*q+152 ∧ x10 = 162*q+76 ∧ x11 = 81*q+38 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_1010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `10100101001`. -/
theorem parameters_10100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+123 ∧ x1 = 384*q+370 ∧ x2 = 192*q+185 ∧ x3 = 576*q+556 ∧ x4 = 288*q+278 ∧ x5 = 144*q+139 ∧ x6 = 432*q+418 ∧ x7 = 216*q+209 ∧ x8 = 648*q+628 ∧ x9 = 324*q+314 ∧ x10 = 162*q+157 ∧ x11 = 486*q+472 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_1010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hstep := r10.1
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    omega

/-- Exact source residue and full affine trace for branch `001001010010`. -/
theorem parameters_001001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
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
    : ∃ q : Nat, x0 = 256*q+228 ∧ x1 = 128*q+114 ∧ x2 = 64*q+57 ∧ x3 = 192*q+172 ∧ x4 = 96*q+86 ∧ x5 = 48*q+43 ∧ x6 = 144*q+130 ∧ x7 = 72*q+65 ∧ x8 = 216*q+196 ∧ x9 = 108*q+98 ∧ x10 = 54*q+49 ∧ x11 = 162*q+148 ∧ x12 = 81*q+74 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_00100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hstep := r11.1
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega

/-- Exact source residue and full affine trace for branch `001010010010`. -/
theorem parameters_001010010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
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
    : ∃ q : Nat, x0 = 256*q+172 ∧ x1 = 128*q+86 ∧ x2 = 64*q+43 ∧ x3 = 192*q+130 ∧ x4 = 96*q+65 ∧ x5 = 288*q+196 ∧ x6 = 144*q+98 ∧ x7 = 72*q+49 ∧ x8 = 216*q+148 ∧ x9 = 108*q+74 ∧ x10 = 54*q+37 ∧ x11 = 162*q+112 ∧ x12 = 81*q+56 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_00101001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hstep := r11.1
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega

/-- Exact source residue and full affine trace for branch `001010010100`. -/
theorem parameters_001010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
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
    : ∃ q : Nat, x0 = 256*q+236 ∧ x1 = 128*q+118 ∧ x2 = 64*q+59 ∧ x3 = 192*q+178 ∧ x4 = 96*q+89 ∧ x5 = 288*q+268 ∧ x6 = 144*q+134 ∧ x7 = 72*q+67 ∧ x8 = 216*q+202 ∧ x9 = 108*q+101 ∧ x10 = 324*q+304 ∧ x11 = 162*q+152 ∧ x12 = 81*q+76 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_00101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hstep := r11.1
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega

/-- Exact source residue and full affine trace for branch `001010010101`. -/
theorem parameters_001010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
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
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    : ∃ q : Nat, x0 = 256*q+108 ∧ x1 = 128*q+54 ∧ x2 = 64*q+27 ∧ x3 = 192*q+82 ∧ x4 = 96*q+41 ∧ x5 = 288*q+124 ∧ x6 = 144*q+62 ∧ x7 = 72*q+31 ∧ x8 = 216*q+94 ∧ x9 = 108*q+47 ∧ x10 = 324*q+142 ∧ x11 = 162*q+71 ∧ x12 = 486*q+214 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_00101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hstep := r11.1
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega

/-- Exact source residue and full affine trace for branch `010010010100`. -/
theorem parameters_010010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
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
    : ∃ q : Nat, x0 = 256*q+66 ∧ x1 = 128*q+33 ∧ x2 = 384*q+100 ∧ x3 = 192*q+50 ∧ x4 = 96*q+25 ∧ x5 = 288*q+76 ∧ x6 = 144*q+38 ∧ x7 = 72*q+19 ∧ x8 = 216*q+58 ∧ x9 = 108*q+29 ∧ x10 = 324*q+88 ∧ x11 = 162*q+44 ∧ x12 = 81*q+22 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_01001001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hstep := r11.1
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega

/-- Exact source residue and full affine trace for branch `010010010101`. -/
theorem parameters_010010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
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
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    : ∃ q : Nat, x0 = 256*q+194 ∧ x1 = 128*q+97 ∧ x2 = 384*q+292 ∧ x3 = 192*q+146 ∧ x4 = 96*q+73 ∧ x5 = 288*q+220 ∧ x6 = 144*q+110 ∧ x7 = 72*q+55 ∧ x8 = 216*q+166 ∧ x9 = 108*q+83 ∧ x10 = 324*q+250 ∧ x11 = 162*q+125 ∧ x12 = 486*q+376 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_01001001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hstep := r11.1
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega

/-- Exact source residue and full affine trace for branch `010010100100`. -/
theorem parameters_010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
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
    : ∃ q : Nat, x0 = 256*q+114 ∧ x1 = 128*q+57 ∧ x2 = 384*q+172 ∧ x3 = 192*q+86 ∧ x4 = 96*q+43 ∧ x5 = 288*q+130 ∧ x6 = 144*q+65 ∧ x7 = 432*q+196 ∧ x8 = 216*q+98 ∧ x9 = 108*q+49 ∧ x10 = 324*q+148 ∧ x11 = 162*q+74 ∧ x12 = 81*q+37 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_01001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hstep := r11.1
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega

/-- Exact source residue and full affine trace for branch `010010100101`. -/
theorem parameters_010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
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
    : ∃ q : Nat, x0 = 256*q+242 ∧ x1 = 128*q+121 ∧ x2 = 384*q+364 ∧ x3 = 192*q+182 ∧ x4 = 96*q+91 ∧ x5 = 288*q+274 ∧ x6 = 144*q+137 ∧ x7 = 432*q+412 ∧ x8 = 216*q+206 ∧ x9 = 108*q+103 ∧ x10 = 324*q+310 ∧ x11 = 162*q+155 ∧ x12 = 486*q+466 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_01001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hstep := r11.1
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
    omega


end Collatz.Exploration.ElevenHalvesArithmetic
