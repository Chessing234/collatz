import Collatz.Exploration.ElevenHalvesArithmetic.Part00

namespace Collatz.Exploration.ElevenHalvesArithmetic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- Exact source residue and full affine trace for branch `00100101`. -/
theorem parameters_00100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    : ∃ q : Nat, x0 = 64*q+36 ∧ x1 = 32*q+18 ∧ x2 = 16*q+9 ∧ x3 = 48*q+28 ∧ x4 = 24*q+14 ∧ x5 = 12*q+7 ∧ x6 = 36*q+22 ∧ x7 = 18*q+11 ∧ x8 = 54*q+34 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_0010010 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hstep := r7.1
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · clear p0 p1 p2 p3 p4 p5 p6
    omega

/-- Exact source residue and full affine trace for branch `00101000`. -/
theorem parameters_00101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    : ∃ q : Nat, x0 = 64*q+12 ∧ x1 = 32*q+6 ∧ x2 = 16*q+3 ∧ x3 = 48*q+10 ∧ x4 = 24*q+5 ∧ x5 = 72*q+16 ∧ x6 = 36*q+8 ∧ x7 = 18*q+4 ∧ x8 = 9*q+2 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_0010100 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hstep := r7.1
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · clear p0 p1 p2 p3 p4 p5 p6
    omega

/-- Exact source residue and full affine trace for branch `00101001`. -/
theorem parameters_00101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    : ∃ q : Nat, x0 = 64*q+44 ∧ x1 = 32*q+22 ∧ x2 = 16*q+11 ∧ x3 = 48*q+34 ∧ x4 = 24*q+17 ∧ x5 = 72*q+52 ∧ x6 = 36*q+26 ∧ x7 = 18*q+13 ∧ x8 = 54*q+40 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_0010100 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hstep := r7.1
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · clear p0 p1 p2 p3 p4 p5 p6
    omega

/-- Exact source residue and full affine trace for branch `01001000`. -/
theorem parameters_01001000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    : ∃ q : Nat, x0 = 64*q+34 ∧ x1 = 32*q+17 ∧ x2 = 96*q+52 ∧ x3 = 48*q+26 ∧ x4 = 24*q+13 ∧ x5 = 72*q+40 ∧ x6 = 36*q+20 ∧ x7 = 18*q+10 ∧ x8 = 9*q+5 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_0100100 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hstep := r7.1
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · clear p0 p1 p2 p3 p4 p5 p6
    omega

/-- Exact source residue and full affine trace for branch `01001001`. -/
theorem parameters_01001001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    : ∃ q : Nat, x0 = 64*q+2 ∧ x1 = 32*q+1 ∧ x2 = 96*q+4 ∧ x3 = 48*q+2 ∧ x4 = 24*q+1 ∧ x5 = 72*q+4 ∧ x6 = 36*q+2 ∧ x7 = 18*q+1 ∧ x8 = 54*q+4 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_0100100 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hstep := r7.1
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · clear p0 p1 p2 p3 p4 p5 p6
    omega

/-- Exact source residue and full affine trace for branch `01001010`. -/
theorem parameters_01001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    : ∃ q : Nat, x0 = 32*q+18 ∧ x1 = 16*q+9 ∧ x2 = 48*q+28 ∧ x3 = 24*q+14 ∧ x4 = 12*q+7 ∧ x5 = 36*q+22 ∧ x6 = 18*q+11 ∧ x7 = 54*q+34 ∧ x8 = 27*q+17 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_0100101 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hstep := r7.1
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · clear p0 p1 p2 p3 p4 p5 p6
    omega

/-- Exact source residue and full affine trace for branch `01010010`. -/
theorem parameters_01010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    : ∃ q : Nat, x0 = 32*q+22 ∧ x1 = 16*q+11 ∧ x2 = 48*q+34 ∧ x3 = 24*q+17 ∧ x4 = 72*q+52 ∧ x5 = 36*q+26 ∧ x6 = 18*q+13 ∧ x7 = 54*q+40 ∧ x8 = 27*q+20 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_0101001 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hstep := r7.1
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · clear p0 p1 p2 p3 p4 p5 p6
    omega

/-- Exact source residue and full affine trace for branch `10010010`. -/
theorem parameters_10010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    : ∃ q : Nat, x0 = 32*q+1 ∧ x1 = 96*q+4 ∧ x2 = 48*q+2 ∧ x3 = 24*q+1 ∧ x4 = 72*q+4 ∧ x5 = 36*q+2 ∧ x6 = 18*q+1 ∧ x7 = 54*q+4 ∧ x8 = 27*q+2 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_1001001 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hstep := r7.1
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · clear p0 p1 p2 p3 p4 p5 p6
    omega

/-- Exact source residue and full affine trace for branch `10010100`. -/
theorem parameters_10010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    : ∃ q : Nat, x0 = 32*q+25 ∧ x1 = 96*q+76 ∧ x2 = 48*q+38 ∧ x3 = 24*q+19 ∧ x4 = 72*q+58 ∧ x5 = 36*q+29 ∧ x6 = 108*q+88 ∧ x7 = 54*q+44 ∧ x8 = 27*q+22 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_1001010 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hstep := r7.1
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · clear p0 p1 p2 p3 p4 p5 p6
    omega

/-- Exact source residue and full affine trace for branch `10010101`. -/
theorem parameters_10010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    : ∃ q : Nat, x0 = 32*q+9 ∧ x1 = 96*q+28 ∧ x2 = 48*q+14 ∧ x3 = 24*q+7 ∧ x4 = 72*q+22 ∧ x5 = 36*q+11 ∧ x6 = 108*q+34 ∧ x7 = 54*q+17 ∧ x8 = 162*q+52 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_1001010 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hstep := r7.1
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · clear p0 p1 p2 p3 p4 p5 p6
    omega

/-- Exact source residue and full affine trace for branch `10100100`. -/
theorem parameters_10100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    : ∃ q : Nat, x0 = 32*q+11 ∧ x1 = 96*q+34 ∧ x2 = 48*q+17 ∧ x3 = 144*q+52 ∧ x4 = 72*q+26 ∧ x5 = 36*q+13 ∧ x6 = 108*q+40 ∧ x7 = 54*q+20 ∧ x8 = 27*q+10 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_1010010 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hstep := r7.1
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · clear p0 p1 p2 p3 p4 p5 p6
    omega

/-- Exact source residue and full affine trace for branch `10100101`. -/
theorem parameters_10100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    : ∃ q : Nat, x0 = 32*q+27 ∧ x1 = 96*q+82 ∧ x2 = 48*q+41 ∧ x3 = 144*q+124 ∧ x4 = 72*q+62 ∧ x5 = 36*q+31 ∧ x6 = 108*q+94 ∧ x7 = 54*q+47 ∧ x8 = 162*q+142 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_1010010 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hstep := r7.1
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · clear p0 p1 p2 p3 p4 p5 p6
    omega

/-- Exact source residue and full affine trace for branch `001001010`. -/
theorem parameters_001001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    : ∃ q : Nat, x0 = 64*q+36 ∧ x1 = 32*q+18 ∧ x2 = 16*q+9 ∧ x3 = 48*q+28 ∧ x4 = 24*q+14 ∧ x5 = 12*q+7 ∧ x6 = 36*q+22 ∧ x7 = 18*q+11 ∧ x8 = 54*q+34 ∧ x9 = 27*q+17 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_00100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `001010010`. -/
theorem parameters_001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    : ∃ q : Nat, x0 = 64*q+44 ∧ x1 = 32*q+22 ∧ x2 = 16*q+11 ∧ x3 = 48*q+34 ∧ x4 = 24*q+17 ∧ x5 = 72*q+52 ∧ x6 = 36*q+26 ∧ x7 = 18*q+13 ∧ x8 = 54*q+40 ∧ x9 = 27*q+20 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_00101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `010010010`. -/
theorem parameters_010010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    : ∃ q : Nat, x0 = 64*q+2 ∧ x1 = 32*q+1 ∧ x2 = 96*q+4 ∧ x3 = 48*q+2 ∧ x4 = 24*q+1 ∧ x5 = 72*q+4 ∧ x6 = 36*q+2 ∧ x7 = 18*q+1 ∧ x8 = 54*q+4 ∧ x9 = 27*q+2 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_01001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `010010100`. -/
theorem parameters_010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    : ∃ q : Nat, x0 = 64*q+50 ∧ x1 = 32*q+25 ∧ x2 = 96*q+76 ∧ x3 = 48*q+38 ∧ x4 = 24*q+19 ∧ x5 = 72*q+58 ∧ x6 = 36*q+29 ∧ x7 = 108*q+88 ∧ x8 = 54*q+44 ∧ x9 = 27*q+22 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_01001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `010010101`. -/
theorem parameters_010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    : ∃ q : Nat, x0 = 64*q+18 ∧ x1 = 32*q+9 ∧ x2 = 96*q+28 ∧ x3 = 48*q+14 ∧ x4 = 24*q+7 ∧ x5 = 72*q+22 ∧ x6 = 36*q+11 ∧ x7 = 108*q+34 ∧ x8 = 54*q+17 ∧ x9 = 162*q+52 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_01001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `010100100`. -/
theorem parameters_010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    : ∃ q : Nat, x0 = 64*q+22 ∧ x1 = 32*q+11 ∧ x2 = 96*q+34 ∧ x3 = 48*q+17 ∧ x4 = 144*q+52 ∧ x5 = 72*q+26 ∧ x6 = 36*q+13 ∧ x7 = 108*q+40 ∧ x8 = 54*q+20 ∧ x9 = 27*q+10 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_01010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `010100101`. -/
theorem parameters_010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    : ∃ q : Nat, x0 = 64*q+54 ∧ x1 = 32*q+27 ∧ x2 = 96*q+82 ∧ x3 = 48*q+41 ∧ x4 = 144*q+124 ∧ x5 = 72*q+62 ∧ x6 = 36*q+31 ∧ x7 = 108*q+94 ∧ x8 = 54*q+47 ∧ x9 = 162*q+142 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_01010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `100100100`. -/
theorem parameters_100100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    : ∃ q : Nat, x0 = 64*q+1 ∧ x1 = 192*q+4 ∧ x2 = 96*q+2 ∧ x3 = 48*q+1 ∧ x4 = 144*q+4 ∧ x5 = 72*q+2 ∧ x6 = 36*q+1 ∧ x7 = 108*q+4 ∧ x8 = 54*q+2 ∧ x9 = 27*q+1 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_10010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `100100101`. -/
theorem parameters_100100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    : ∃ q : Nat, x0 = 64*q+33 ∧ x1 = 192*q+100 ∧ x2 = 96*q+50 ∧ x3 = 48*q+25 ∧ x4 = 144*q+76 ∧ x5 = 72*q+38 ∧ x6 = 36*q+19 ∧ x7 = 108*q+58 ∧ x8 = 54*q+29 ∧ x9 = 162*q+88 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_10010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `100101000`. -/
theorem parameters_100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    : ∃ q : Nat, x0 = 64*q+25 ∧ x1 = 192*q+76 ∧ x2 = 96*q+38 ∧ x3 = 48*q+19 ∧ x4 = 144*q+58 ∧ x5 = 72*q+29 ∧ x6 = 216*q+88 ∧ x7 = 108*q+44 ∧ x8 = 54*q+22 ∧ x9 = 27*q+11 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_10010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `100101001`. -/
theorem parameters_100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    : ∃ q : Nat, x0 = 64*q+57 ∧ x1 = 192*q+172 ∧ x2 = 96*q+86 ∧ x3 = 48*q+43 ∧ x4 = 144*q+130 ∧ x5 = 72*q+65 ∧ x6 = 216*q+196 ∧ x7 = 108*q+98 ∧ x8 = 54*q+49 ∧ x9 = 162*q+148 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_10010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `101001000`. -/
theorem parameters_101001000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    : ∃ q : Nat, x0 = 64*q+11 ∧ x1 = 192*q+34 ∧ x2 = 96*q+17 ∧ x3 = 288*q+52 ∧ x4 = 144*q+26 ∧ x5 = 72*q+13 ∧ x6 = 216*q+40 ∧ x7 = 108*q+20 ∧ x8 = 54*q+10 ∧ x9 = 27*q+5 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_10100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `101001001`. -/
theorem parameters_101001001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    : ∃ q : Nat, x0 = 64*q+43 ∧ x1 = 192*q+130 ∧ x2 = 96*q+65 ∧ x3 = 288*q+196 ∧ x4 = 144*q+98 ∧ x5 = 72*q+49 ∧ x6 = 216*q+148 ∧ x7 = 108*q+74 ∧ x8 = 54*q+37 ∧ x9 = 162*q+112 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_10100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `101001010`. -/
theorem parameters_101001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    : ∃ q : Nat, x0 = 32*q+27 ∧ x1 = 96*q+82 ∧ x2 = 48*q+41 ∧ x3 = 144*q+124 ∧ x4 = 72*q+62 ∧ x5 = 36*q+31 ∧ x6 = 108*q+94 ∧ x7 = 54*q+47 ∧ x8 = 162*q+142 ∧ x9 = 81*q+71 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_10100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hstep := r8.1
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · clear p0 p1 p2 p3 p4 p5 p6 p7
    omega

/-- Exact source residue and full affine trace for branch `0010010100`. -/
theorem parameters_0010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+100 ∧ x1 = 64*q+50 ∧ x2 = 32*q+25 ∧ x3 = 96*q+76 ∧ x4 = 48*q+38 ∧ x5 = 24*q+19 ∧ x6 = 72*q+58 ∧ x7 = 36*q+29 ∧ x8 = 108*q+88 ∧ x9 = 54*q+44 ∧ x10 = 27*q+22 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_001001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
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

/-- Exact source residue and full affine trace for branch `0010010101`. -/
theorem parameters_0010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    : ∃ q : Nat, x0 = 128*q+36 ∧ x1 = 64*q+18 ∧ x2 = 32*q+9 ∧ x3 = 96*q+28 ∧ x4 = 48*q+14 ∧ x5 = 24*q+7 ∧ x6 = 72*q+22 ∧ x7 = 36*q+11 ∧ x8 = 108*q+34 ∧ x9 = 54*q+17 ∧ x10 = 162*q+52 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_001001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
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

/-- Exact source residue and full affine trace for branch `0010100100`. -/
theorem parameters_0010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+44 ∧ x1 = 64*q+22 ∧ x2 = 32*q+11 ∧ x3 = 96*q+34 ∧ x4 = 48*q+17 ∧ x5 = 144*q+52 ∧ x6 = 72*q+26 ∧ x7 = 36*q+13 ∧ x8 = 108*q+40 ∧ x9 = 54*q+20 ∧ x10 = 27*q+10 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
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

/-- Exact source residue and full affine trace for branch `0010100101`. -/
theorem parameters_0010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+108 ∧ x1 = 64*q+54 ∧ x2 = 32*q+27 ∧ x3 = 96*q+82 ∧ x4 = 48*q+41 ∧ x5 = 144*q+124 ∧ x6 = 72*q+62 ∧ x7 = 36*q+31 ∧ x8 = 108*q+94 ∧ x9 = 54*q+47 ∧ x10 = 162*q+142 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
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

/-- Exact source residue and full affine trace for branch `0100100100`. -/
theorem parameters_0100100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    : ∃ q : Nat, x0 = 128*q+2 ∧ x1 = 64*q+1 ∧ x2 = 192*q+4 ∧ x3 = 96*q+2 ∧ x4 = 48*q+1 ∧ x5 = 144*q+4 ∧ x6 = 72*q+2 ∧ x7 = 36*q+1 ∧ x8 = 108*q+4 ∧ x9 = 54*q+2 ∧ x10 = 27*q+1 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_010010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
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

/-- Exact source residue and full affine trace for branch `0100100101`. -/
theorem parameters_0100100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+66 ∧ x1 = 64*q+33 ∧ x2 = 192*q+100 ∧ x3 = 96*q+50 ∧ x4 = 48*q+25 ∧ x5 = 144*q+76 ∧ x6 = 72*q+38 ∧ x7 = 36*q+19 ∧ x8 = 108*q+58 ∧ x9 = 54*q+29 ∧ x10 = 162*q+88 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_010010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
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

/-- Exact source residue and full affine trace for branch `0100101000`. -/
theorem parameters_0100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    : ∃ q : Nat, x0 = 128*q+50 ∧ x1 = 64*q+25 ∧ x2 = 192*q+76 ∧ x3 = 96*q+38 ∧ x4 = 48*q+19 ∧ x5 = 144*q+58 ∧ x6 = 72*q+29 ∧ x7 = 216*q+88 ∧ x8 = 108*q+44 ∧ x9 = 54*q+22 ∧ x10 = 27*q+11 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
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

/-- Exact source residue and full affine trace for branch `0100101001`. -/
theorem parameters_0100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+114 ∧ x1 = 64*q+57 ∧ x2 = 192*q+172 ∧ x3 = 96*q+86 ∧ x4 = 48*q+43 ∧ x5 = 144*q+130 ∧ x6 = 72*q+65 ∧ x7 = 216*q+196 ∧ x8 = 108*q+98 ∧ x9 = 54*q+49 ∧ x10 = 162*q+148 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
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

/-- Exact source residue and full affine trace for branch `0101001000`. -/
theorem parameters_0101001000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    : ∃ q : Nat, x0 = 128*q+22 ∧ x1 = 64*q+11 ∧ x2 = 192*q+34 ∧ x3 = 96*q+17 ∧ x4 = 288*q+52 ∧ x5 = 144*q+26 ∧ x6 = 72*q+13 ∧ x7 = 216*q+40 ∧ x8 = 108*q+20 ∧ x9 = 54*q+10 ∧ x10 = 27*q+5 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
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

/-- Exact source residue and full affine trace for branch `0101001001`. -/
theorem parameters_0101001001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+86 ∧ x1 = 64*q+43 ∧ x2 = 192*q+130 ∧ x3 = 96*q+65 ∧ x4 = 288*q+196 ∧ x5 = 144*q+98 ∧ x6 = 72*q+49 ∧ x7 = 216*q+148 ∧ x8 = 108*q+74 ∧ x9 = 54*q+37 ∧ x10 = 162*q+112 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
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


end Collatz.Exploration.ElevenHalvesArithmetic
