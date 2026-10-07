import Collatz.Basic

/-! Generated residue-and-affine certificates for the inclusive ratio-21/4 band.
Every branch and arithmetic conclusion is independently checked by Lean. -/
namespace Collatz.Exploration.WiderBandArithmetic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- Exact source residue and full affine trace for branch `0`. -/
theorem parameters_0
    (x0 x1 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    : ∃ q : Nat, x0 = 2*q+0 ∧ x1 = 1*q+0 := by
  let q := x0
  have p0 : x0 = q := rfl
  have hstep := r0.1
  have hparity := r0.2
  clear r0
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1`. -/
theorem parameters_1
    (x0 x1 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    : ∃ q : Nat, x0 = 2*q+1 ∧ x1 = 6*q+4 := by
  let q := x0
  have p0 : x0 = q := rfl
  have hstep := r0.1
  have hparity := r0.2
  clear r0
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `00`. -/
theorem parameters_00
    (x0 x1 x2 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    : ∃ q : Nat, x0 = 4*q+0 ∧ x1 = 2*q+0 ∧ x2 = 1*q+0 := by
  obtain ⟨q,p0,p1⟩ := parameters_0 x0 x1 r0
  have hstep := r1.1
  have hparity := r1.2
  clear r0 r1
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `01`. -/
theorem parameters_01
    (x0 x1 x2 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    : ∃ q : Nat, x0 = 4*q+2 ∧ x1 = 2*q+1 ∧ x2 = 6*q+4 := by
  obtain ⟨q,p0,p1⟩ := parameters_0 x0 x1 r0
  have hstep := r1.1
  have hparity := r1.2
  clear r0 r1
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `10`. -/
theorem parameters_10
    (x0 x1 x2 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    : ∃ q : Nat, x0 = 2*q+1 ∧ x1 = 6*q+4 ∧ x2 = 3*q+2 := by
  obtain ⟨q,p0,p1⟩ := parameters_1 x0 x1 r0
  have hstep := r1.1
  have hparity := r1.2
  clear r0 r1
  clear hparity
  refine ⟨q,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `000`. -/
theorem parameters_000
    (x0 x1 x2 x3 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    : ∃ q : Nat, x0 = 8*q+0 ∧ x1 = 4*q+0 ∧ x2 = 2*q+0 ∧ x3 = 1*q+0 := by
  obtain ⟨q,p0,p1,p2⟩ := parameters_00 x0 x1 x2 r0 r1
  have hstep := r2.1
  have hparity := r2.2
  clear r0 r1 r2
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `001`. -/
theorem parameters_001
    (x0 x1 x2 x3 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    : ∃ q : Nat, x0 = 8*q+4 ∧ x1 = 4*q+2 ∧ x2 = 2*q+1 ∧ x3 = 6*q+4 := by
  obtain ⟨q,p0,p1,p2⟩ := parameters_00 x0 x1 x2 r0 r1
  have hstep := r2.1
  have hparity := r2.2
  clear r0 r1 r2
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `010`. -/
theorem parameters_010
    (x0 x1 x2 x3 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    : ∃ q : Nat, x0 = 4*q+2 ∧ x1 = 2*q+1 ∧ x2 = 6*q+4 ∧ x3 = 3*q+2 := by
  obtain ⟨q,p0,p1,p2⟩ := parameters_01 x0 x1 x2 r0 r1
  have hstep := r2.1
  have hparity := r2.2
  clear r0 r1 r2
  clear hparity
  refine ⟨q,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `100`. -/
theorem parameters_100
    (x0 x1 x2 x3 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    : ∃ q : Nat, x0 = 4*q+1 ∧ x1 = 12*q+4 ∧ x2 = 6*q+2 ∧ x3 = 3*q+1 := by
  obtain ⟨q,p0,p1,p2⟩ := parameters_10 x0 x1 x2 r0 r1
  have hstep := r2.1
  have hparity := r2.2
  clear r0 r1 r2
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `101`. -/
theorem parameters_101
    (x0 x1 x2 x3 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    : ∃ q : Nat, x0 = 4*q+3 ∧ x1 = 12*q+10 ∧ x2 = 6*q+5 ∧ x3 = 18*q+16 := by
  obtain ⟨q,p0,p1,p2⟩ := parameters_10 x0 x1 x2 r0 r1
  have hstep := r2.1
  have hparity := r2.2
  clear r0 r1 r2
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0010`. -/
theorem parameters_0010
    (x0 x1 x2 x3 x4 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    : ∃ q : Nat, x0 = 8*q+4 ∧ x1 = 4*q+2 ∧ x2 = 2*q+1 ∧ x3 = 6*q+4 ∧ x4 = 3*q+2 := by
  obtain ⟨q,p0,p1,p2,p3⟩ := parameters_001 x0 x1 x2 x3 r0 r1 r2
  have hstep := r3.1
  have hparity := r3.2
  clear r0 r1 r2 r3
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0100`. -/
theorem parameters_0100
    (x0 x1 x2 x3 x4 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    : ∃ q : Nat, x0 = 8*q+2 ∧ x1 = 4*q+1 ∧ x2 = 12*q+4 ∧ x3 = 6*q+2 ∧ x4 = 3*q+1 := by
  obtain ⟨q,p0,p1,p2,p3⟩ := parameters_010 x0 x1 x2 x3 r0 r1 r2
  have hstep := r3.1
  have hparity := r3.2
  clear r0 r1 r2 r3
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0101`. -/
theorem parameters_0101
    (x0 x1 x2 x3 x4 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    : ∃ q : Nat, x0 = 8*q+6 ∧ x1 = 4*q+3 ∧ x2 = 12*q+10 ∧ x3 = 6*q+5 ∧ x4 = 18*q+16 := by
  obtain ⟨q,p0,p1,p2,p3⟩ := parameters_010 x0 x1 x2 x3 r0 r1 r2
  have hstep := r3.1
  have hparity := r3.2
  clear r0 r1 r2 r3
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1000`. -/
theorem parameters_1000
    (x0 x1 x2 x3 x4 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    : ∃ q : Nat, x0 = 8*q+5 ∧ x1 = 24*q+16 ∧ x2 = 12*q+8 ∧ x3 = 6*q+4 ∧ x4 = 3*q+2 := by
  obtain ⟨q,p0,p1,p2,p3⟩ := parameters_100 x0 x1 x2 x3 r0 r1 r2
  have hstep := r3.1
  have hparity := r3.2
  clear r0 r1 r2 r3
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1001`. -/
theorem parameters_1001
    (x0 x1 x2 x3 x4 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    : ∃ q : Nat, x0 = 8*q+1 ∧ x1 = 24*q+4 ∧ x2 = 12*q+2 ∧ x3 = 6*q+1 ∧ x4 = 18*q+4 := by
  obtain ⟨q,p0,p1,p2,p3⟩ := parameters_100 x0 x1 x2 x3 r0 r1 r2
  have hstep := r3.1
  have hparity := r3.2
  clear r0 r1 r2 r3
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1010`. -/
theorem parameters_1010
    (x0 x1 x2 x3 x4 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    : ∃ q : Nat, x0 = 4*q+3 ∧ x1 = 12*q+10 ∧ x2 = 6*q+5 ∧ x3 = 18*q+16 ∧ x4 = 9*q+8 := by
  obtain ⟨q,p0,p1,p2,p3⟩ := parameters_101 x0 x1 x2 x3 r0 r1 r2
  have hstep := r3.1
  have hparity := r3.2
  clear r0 r1 r2 r3
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `00100`. -/
theorem parameters_00100
    (x0 x1 x2 x3 x4 x5 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    : ∃ q : Nat, x0 = 16*q+4 ∧ x1 = 8*q+2 ∧ x2 = 4*q+1 ∧ x3 = 12*q+4 ∧ x4 = 6*q+2 ∧ x5 = 3*q+1 := by
  obtain ⟨q,p0,p1,p2,p3,p4⟩ := parameters_0010 x0 x1 x2 x3 x4 r0 r1 r2 r3
  have hstep := r4.1
  have hparity := r4.2
  clear r0 r1 r2 r3 r4
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `00101`. -/
theorem parameters_00101
    (x0 x1 x2 x3 x4 x5 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    : ∃ q : Nat, x0 = 16*q+12 ∧ x1 = 8*q+6 ∧ x2 = 4*q+3 ∧ x3 = 12*q+10 ∧ x4 = 6*q+5 ∧ x5 = 18*q+16 := by
  obtain ⟨q,p0,p1,p2,p3,p4⟩ := parameters_0010 x0 x1 x2 x3 x4 r0 r1 r2 r3
  have hstep := r4.1
  have hparity := r4.2
  clear r0 r1 r2 r3 r4
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `01000`. -/
theorem parameters_01000
    (x0 x1 x2 x3 x4 x5 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    : ∃ q : Nat, x0 = 16*q+10 ∧ x1 = 8*q+5 ∧ x2 = 24*q+16 ∧ x3 = 12*q+8 ∧ x4 = 6*q+4 ∧ x5 = 3*q+2 := by
  obtain ⟨q,p0,p1,p2,p3,p4⟩ := parameters_0100 x0 x1 x2 x3 x4 r0 r1 r2 r3
  have hstep := r4.1
  have hparity := r4.2
  clear r0 r1 r2 r3 r4
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `01001`. -/
theorem parameters_01001
    (x0 x1 x2 x3 x4 x5 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    : ∃ q : Nat, x0 = 16*q+2 ∧ x1 = 8*q+1 ∧ x2 = 24*q+4 ∧ x3 = 12*q+2 ∧ x4 = 6*q+1 ∧ x5 = 18*q+4 := by
  obtain ⟨q,p0,p1,p2,p3,p4⟩ := parameters_0100 x0 x1 x2 x3 x4 r0 r1 r2 r3
  have hstep := r4.1
  have hparity := r4.2
  clear r0 r1 r2 r3 r4
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `01010`. -/
theorem parameters_01010
    (x0 x1 x2 x3 x4 x5 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    : ∃ q : Nat, x0 = 8*q+6 ∧ x1 = 4*q+3 ∧ x2 = 12*q+10 ∧ x3 = 6*q+5 ∧ x4 = 18*q+16 ∧ x5 = 9*q+8 := by
  obtain ⟨q,p0,p1,p2,p3,p4⟩ := parameters_0101 x0 x1 x2 x3 x4 r0 r1 r2 r3
  have hstep := r4.1
  have hparity := r4.2
  clear r0 r1 r2 r3 r4
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `10010`. -/
theorem parameters_10010
    (x0 x1 x2 x3 x4 x5 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    : ∃ q : Nat, x0 = 8*q+1 ∧ x1 = 24*q+4 ∧ x2 = 12*q+2 ∧ x3 = 6*q+1 ∧ x4 = 18*q+4 ∧ x5 = 9*q+2 := by
  obtain ⟨q,p0,p1,p2,p3,p4⟩ := parameters_1001 x0 x1 x2 x3 x4 r0 r1 r2 r3
  have hstep := r4.1
  have hparity := r4.2
  clear r0 r1 r2 r3 r4
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `10100`. -/
theorem parameters_10100
    (x0 x1 x2 x3 x4 x5 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    : ∃ q : Nat, x0 = 8*q+3 ∧ x1 = 24*q+10 ∧ x2 = 12*q+5 ∧ x3 = 36*q+16 ∧ x4 = 18*q+8 ∧ x5 = 9*q+4 := by
  obtain ⟨q,p0,p1,p2,p3,p4⟩ := parameters_1010 x0 x1 x2 x3 x4 r0 r1 r2 r3
  have hstep := r4.1
  have hparity := r4.2
  clear r0 r1 r2 r3 r4
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `10101`. -/
theorem parameters_10101
    (x0 x1 x2 x3 x4 x5 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    : ∃ q : Nat, x0 = 8*q+7 ∧ x1 = 24*q+22 ∧ x2 = 12*q+11 ∧ x3 = 36*q+34 ∧ x4 = 18*q+17 ∧ x5 = 54*q+52 := by
  obtain ⟨q,p0,p1,p2,p3,p4⟩ := parameters_1010 x0 x1 x2 x3 x4 r0 r1 r2 r3
  have hstep := r4.1
  have hparity := r4.2
  clear r0 r1 r2 r3 r4
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `001000`. -/
theorem parameters_001000
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    : ∃ q : Nat, x0 = 32*q+20 ∧ x1 = 16*q+10 ∧ x2 = 8*q+5 ∧ x3 = 24*q+16 ∧ x4 = 12*q+8 ∧ x5 = 6*q+4 ∧ x6 = 3*q+2 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_00100 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  have hstep := r5.1
  have hparity := r5.2
  clear r0 r1 r2 r3 r4 r5
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `001001`. -/
theorem parameters_001001
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    : ∃ q : Nat, x0 = 32*q+4 ∧ x1 = 16*q+2 ∧ x2 = 8*q+1 ∧ x3 = 24*q+4 ∧ x4 = 12*q+2 ∧ x5 = 6*q+1 ∧ x6 = 18*q+4 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_00100 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  have hstep := r5.1
  have hparity := r5.2
  clear r0 r1 r2 r3 r4 r5
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `001010`. -/
theorem parameters_001010
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    : ∃ q : Nat, x0 = 16*q+12 ∧ x1 = 8*q+6 ∧ x2 = 4*q+3 ∧ x3 = 12*q+10 ∧ x4 = 6*q+5 ∧ x5 = 18*q+16 ∧ x6 = 9*q+8 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_00101 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  have hstep := r5.1
  have hparity := r5.2
  clear r0 r1 r2 r3 r4 r5
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `010010`. -/
theorem parameters_010010
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    : ∃ q : Nat, x0 = 16*q+2 ∧ x1 = 8*q+1 ∧ x2 = 24*q+4 ∧ x3 = 12*q+2 ∧ x4 = 6*q+1 ∧ x5 = 18*q+4 ∧ x6 = 9*q+2 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_01001 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  have hstep := r5.1
  have hparity := r5.2
  clear r0 r1 r2 r3 r4 r5
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `010100`. -/
theorem parameters_010100
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    : ∃ q : Nat, x0 = 16*q+6 ∧ x1 = 8*q+3 ∧ x2 = 24*q+10 ∧ x3 = 12*q+5 ∧ x4 = 36*q+16 ∧ x5 = 18*q+8 ∧ x6 = 9*q+4 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_01010 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  have hstep := r5.1
  have hparity := r5.2
  clear r0 r1 r2 r3 r4 r5
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `010101`. -/
theorem parameters_010101
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    : ∃ q : Nat, x0 = 16*q+14 ∧ x1 = 8*q+7 ∧ x2 = 24*q+22 ∧ x3 = 12*q+11 ∧ x4 = 36*q+34 ∧ x5 = 18*q+17 ∧ x6 = 54*q+52 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_01010 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  have hstep := r5.1
  have hparity := r5.2
  clear r0 r1 r2 r3 r4 r5
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `100100`. -/
theorem parameters_100100
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    : ∃ q : Nat, x0 = 16*q+1 ∧ x1 = 48*q+4 ∧ x2 = 24*q+2 ∧ x3 = 12*q+1 ∧ x4 = 36*q+4 ∧ x5 = 18*q+2 ∧ x6 = 9*q+1 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_10010 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  have hstep := r5.1
  have hparity := r5.2
  clear r0 r1 r2 r3 r4 r5
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `100101`. -/
theorem parameters_100101
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    : ∃ q : Nat, x0 = 16*q+9 ∧ x1 = 48*q+28 ∧ x2 = 24*q+14 ∧ x3 = 12*q+7 ∧ x4 = 36*q+22 ∧ x5 = 18*q+11 ∧ x6 = 54*q+34 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_10010 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  have hstep := r5.1
  have hparity := r5.2
  clear r0 r1 r2 r3 r4 r5
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `101000`. -/
theorem parameters_101000
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    : ∃ q : Nat, x0 = 16*q+3 ∧ x1 = 48*q+10 ∧ x2 = 24*q+5 ∧ x3 = 72*q+16 ∧ x4 = 36*q+8 ∧ x5 = 18*q+4 ∧ x6 = 9*q+2 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_10100 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  have hstep := r5.1
  have hparity := r5.2
  clear r0 r1 r2 r3 r4 r5
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `101001`. -/
theorem parameters_101001
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    : ∃ q : Nat, x0 = 16*q+11 ∧ x1 = 48*q+34 ∧ x2 = 24*q+17 ∧ x3 = 72*q+52 ∧ x4 = 36*q+26 ∧ x5 = 18*q+13 ∧ x6 = 54*q+40 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_10100 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  have hstep := r5.1
  have hparity := r5.2
  clear r0 r1 r2 r3 r4 r5
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0010010`. -/
theorem parameters_0010010
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    : ∃ q : Nat, x0 = 32*q+4 ∧ x1 = 16*q+2 ∧ x2 = 8*q+1 ∧ x3 = 24*q+4 ∧ x4 = 12*q+2 ∧ x5 = 6*q+1 ∧ x6 = 18*q+4 ∧ x7 = 9*q+2 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_001001 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hstep := r6.1
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0010100`. -/
theorem parameters_0010100
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    : ∃ q : Nat, x0 = 32*q+12 ∧ x1 = 16*q+6 ∧ x2 = 8*q+3 ∧ x3 = 24*q+10 ∧ x4 = 12*q+5 ∧ x5 = 36*q+16 ∧ x6 = 18*q+8 ∧ x7 = 9*q+4 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_001010 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hstep := r6.1
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0010101`. -/
theorem parameters_0010101
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    : ∃ q : Nat, x0 = 32*q+28 ∧ x1 = 16*q+14 ∧ x2 = 8*q+7 ∧ x3 = 24*q+22 ∧ x4 = 12*q+11 ∧ x5 = 36*q+34 ∧ x6 = 18*q+17 ∧ x7 = 54*q+52 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_001010 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hstep := r6.1
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0100100`. -/
theorem parameters_0100100
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    : ∃ q : Nat, x0 = 32*q+2 ∧ x1 = 16*q+1 ∧ x2 = 48*q+4 ∧ x3 = 24*q+2 ∧ x4 = 12*q+1 ∧ x5 = 36*q+4 ∧ x6 = 18*q+2 ∧ x7 = 9*q+1 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_010010 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hstep := r6.1
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0100101`. -/
theorem parameters_0100101
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    : ∃ q : Nat, x0 = 32*q+18 ∧ x1 = 16*q+9 ∧ x2 = 48*q+28 ∧ x3 = 24*q+14 ∧ x4 = 12*q+7 ∧ x5 = 36*q+22 ∧ x6 = 18*q+11 ∧ x7 = 54*q+34 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_010010 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hstep := r6.1
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0101000`. -/
theorem parameters_0101000
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    : ∃ q : Nat, x0 = 32*q+6 ∧ x1 = 16*q+3 ∧ x2 = 48*q+10 ∧ x3 = 24*q+5 ∧ x4 = 72*q+16 ∧ x5 = 36*q+8 ∧ x6 = 18*q+4 ∧ x7 = 9*q+2 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_010100 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hstep := r6.1
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0101001`. -/
theorem parameters_0101001
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    : ∃ q : Nat, x0 = 32*q+22 ∧ x1 = 16*q+11 ∧ x2 = 48*q+34 ∧ x3 = 24*q+17 ∧ x4 = 72*q+52 ∧ x5 = 36*q+26 ∧ x6 = 18*q+13 ∧ x7 = 54*q+40 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_010100 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hstep := r6.1
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1001000`. -/
theorem parameters_1001000
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    : ∃ q : Nat, x0 = 32*q+17 ∧ x1 = 96*q+52 ∧ x2 = 48*q+26 ∧ x3 = 24*q+13 ∧ x4 = 72*q+40 ∧ x5 = 36*q+20 ∧ x6 = 18*q+10 ∧ x7 = 9*q+5 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_100100 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hstep := r6.1
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1001001`. -/
theorem parameters_1001001
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    : ∃ q : Nat, x0 = 32*q+1 ∧ x1 = 96*q+4 ∧ x2 = 48*q+2 ∧ x3 = 24*q+1 ∧ x4 = 72*q+4 ∧ x5 = 36*q+2 ∧ x6 = 18*q+1 ∧ x7 = 54*q+4 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_100100 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hstep := r6.1
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1001010`. -/
theorem parameters_1001010
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    : ∃ q : Nat, x0 = 16*q+9 ∧ x1 = 48*q+28 ∧ x2 = 24*q+14 ∧ x3 = 12*q+7 ∧ x4 = 36*q+22 ∧ x5 = 18*q+11 ∧ x6 = 54*q+34 ∧ x7 = 27*q+17 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_100101 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hstep := r6.1
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1010010`. -/
theorem parameters_1010010
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    : ∃ q : Nat, x0 = 16*q+11 ∧ x1 = 48*q+34 ∧ x2 = 24*q+17 ∧ x3 = 72*q+52 ∧ x4 = 36*q+26 ∧ x5 = 18*q+13 ∧ x6 = 54*q+40 ∧ x7 = 27*q+20 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_101001 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hstep := r6.1
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `00100100`. -/
theorem parameters_00100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    : ∃ q : Nat, x0 = 64*q+4 ∧ x1 = 32*q+2 ∧ x2 = 16*q+1 ∧ x3 = 48*q+4 ∧ x4 = 24*q+2 ∧ x5 = 12*q+1 ∧ x6 = 36*q+4 ∧ x7 = 18*q+2 ∧ x8 = 9*q+1 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_0010010 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hstep := r7.1
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `010100101000`. -/
theorem parameters_010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
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
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    : ∃ q : Nat, x0 = 256*q+118 ∧ x1 = 128*q+59 ∧ x2 = 384*q+178 ∧ x3 = 192*q+89 ∧ x4 = 576*q+268 ∧ x5 = 288*q+134 ∧ x6 = 144*q+67 ∧ x7 = 432*q+202 ∧ x8 = 216*q+101 ∧ x9 = 648*q+304 ∧ x10 = 324*q+152 ∧ x11 = 162*q+76 ∧ x12 = 81*q+38 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_01010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hstep := r11.1
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `010100101001`. -/
theorem parameters_010100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
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
    : ∃ q : Nat, x0 = 256*q+246 ∧ x1 = 128*q+123 ∧ x2 = 384*q+370 ∧ x3 = 192*q+185 ∧ x4 = 576*q+556 ∧ x5 = 288*q+278 ∧ x6 = 144*q+139 ∧ x7 = 432*q+418 ∧ x8 = 216*q+209 ∧ x9 = 648*q+628 ∧ x10 = 324*q+314 ∧ x11 = 162*q+157 ∧ x12 = 486*q+472 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_01010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hstep := r11.1
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `100101001010`. -/
theorem parameters_100101001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+121 ∧ x1 = 384*q+364 ∧ x2 = 192*q+182 ∧ x3 = 96*q+91 ∧ x4 = 288*q+274 ∧ x5 = 144*q+137 ∧ x6 = 432*q+412 ∧ x7 = 216*q+206 ∧ x8 = 108*q+103 ∧ x9 = 324*q+310 ∧ x10 = 162*q+155 ∧ x11 = 486*q+466 ∧ x12 = 243*q+233 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_10010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hstep := r11.1
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `101001010010`. -/
theorem parameters_101001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
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
    : ∃ q : Nat, x0 = 128*q+123 ∧ x1 = 384*q+370 ∧ x2 = 192*q+185 ∧ x3 = 576*q+556 ∧ x4 = 288*q+278 ∧ x5 = 144*q+139 ∧ x6 = 432*q+418 ∧ x7 = 216*q+209 ∧ x8 = 648*q+628 ∧ x9 = 324*q+314 ∧ x10 = 162*q+157 ∧ x11 = 486*q+472 ∧ x12 = 243*q+236 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_10100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hstep := r11.1
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0010100101000`. -/
theorem parameters_0010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
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
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    : ∃ q : Nat, x0 = 512*q+236 ∧ x1 = 256*q+118 ∧ x2 = 128*q+59 ∧ x3 = 384*q+178 ∧ x4 = 192*q+89 ∧ x5 = 576*q+268 ∧ x6 = 288*q+134 ∧ x7 = 144*q+67 ∧ x8 = 432*q+202 ∧ x9 = 216*q+101 ∧ x10 = 648*q+304 ∧ x11 = 324*q+152 ∧ x12 = 162*q+76 ∧ x13 = 81*q+38 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hstep := r12.1
  have hparity := r12.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0010100101001`. -/
theorem parameters_0010100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
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
    : ∃ q : Nat, x0 = 512*q+492 ∧ x1 = 256*q+246 ∧ x2 = 128*q+123 ∧ x3 = 384*q+370 ∧ x4 = 192*q+185 ∧ x5 = 576*q+556 ∧ x6 = 288*q+278 ∧ x7 = 144*q+139 ∧ x8 = 432*q+418 ∧ x9 = 216*q+209 ∧ x10 = 648*q+628 ∧ x11 = 324*q+314 ∧ x12 = 162*q+157 ∧ x13 = 486*q+472 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hstep := r12.1
  have hparity := r12.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0100101001010`. -/
theorem parameters_0100101001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
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
    : ∃ q : Nat, x0 = 256*q+242 ∧ x1 = 128*q+121 ∧ x2 = 384*q+364 ∧ x3 = 192*q+182 ∧ x4 = 96*q+91 ∧ x5 = 288*q+274 ∧ x6 = 144*q+137 ∧ x7 = 432*q+412 ∧ x8 = 216*q+206 ∧ x9 = 108*q+103 ∧ x10 = 324*q+310 ∧ x11 = 162*q+155 ∧ x12 = 486*q+466 ∧ x13 = 243*q+233 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hstep := r12.1
  have hparity := r12.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0101001010010`. -/
theorem parameters_0101001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
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
    : ∃ q : Nat, x0 = 256*q+246 ∧ x1 = 128*q+123 ∧ x2 = 384*q+370 ∧ x3 = 192*q+185 ∧ x4 = 576*q+556 ∧ x5 = 288*q+278 ∧ x6 = 144*q+139 ∧ x7 = 432*q+418 ∧ x8 = 216*q+209 ∧ x9 = 648*q+628 ∧ x10 = 324*q+314 ∧ x11 = 162*q+157 ∧ x12 = 486*q+472 ∧ x13 = 243*q+236 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hstep := r12.1
  have hparity := r12.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1001010010100`. -/
theorem parameters_1001010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
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
    : ∃ q : Nat, x0 = 256*q+249 ∧ x1 = 768*q+748 ∧ x2 = 384*q+374 ∧ x3 = 192*q+187 ∧ x4 = 576*q+562 ∧ x5 = 288*q+281 ∧ x6 = 864*q+844 ∧ x7 = 432*q+422 ∧ x8 = 216*q+211 ∧ x9 = 648*q+634 ∧ x10 = 324*q+317 ∧ x11 = 972*q+952 ∧ x12 = 486*q+476 ∧ x13 = 243*q+238 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_100101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hstep := r12.1
  have hparity := r12.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1001010010101`. -/
theorem parameters_1001010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
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
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    : ∃ q : Nat, x0 = 256*q+121 ∧ x1 = 768*q+364 ∧ x2 = 384*q+182 ∧ x3 = 192*q+91 ∧ x4 = 576*q+274 ∧ x5 = 288*q+137 ∧ x6 = 864*q+412 ∧ x7 = 432*q+206 ∧ x8 = 216*q+103 ∧ x9 = 648*q+310 ∧ x10 = 324*q+155 ∧ x11 = 972*q+466 ∧ x12 = 486*q+233 ∧ x13 = 1458*q+700 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_100101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hstep := r12.1
  have hparity := r12.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1010010100100`. -/
theorem parameters_1010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
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
    : ∃ q : Nat, x0 = 256*q+123 ∧ x1 = 768*q+370 ∧ x2 = 384*q+185 ∧ x3 = 1152*q+556 ∧ x4 = 576*q+278 ∧ x5 = 288*q+139 ∧ x6 = 864*q+418 ∧ x7 = 432*q+209 ∧ x8 = 1296*q+628 ∧ x9 = 648*q+314 ∧ x10 = 324*q+157 ∧ x11 = 972*q+472 ∧ x12 = 486*q+236 ∧ x13 = 243*q+118 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hstep := r12.1
  have hparity := r12.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1010010100101`. -/
theorem parameters_1010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
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
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    : ∃ q : Nat, x0 = 256*q+251 ∧ x1 = 768*q+754 ∧ x2 = 384*q+377 ∧ x3 = 1152*q+1132 ∧ x4 = 576*q+566 ∧ x5 = 288*q+283 ∧ x6 = 864*q+850 ∧ x7 = 432*q+425 ∧ x8 = 1296*q+1276 ∧ x9 = 648*q+638 ∧ x10 = 324*q+319 ∧ x11 = 972*q+958 ∧ x12 = 486*q+479 ∧ x13 = 1458*q+1438 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hstep := r12.1
  have hparity := r12.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `00101001010010`. -/
theorem parameters_00101001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
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
    : ∃ q : Nat, x0 = 512*q+492 ∧ x1 = 256*q+246 ∧ x2 = 128*q+123 ∧ x3 = 384*q+370 ∧ x4 = 192*q+185 ∧ x5 = 576*q+556 ∧ x6 = 288*q+278 ∧ x7 = 144*q+139 ∧ x8 = 432*q+418 ∧ x9 = 216*q+209 ∧ x10 = 648*q+628 ∧ x11 = 324*q+314 ∧ x12 = 162*q+157 ∧ x13 = 486*q+472 ∧ x14 = 243*q+236 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_0010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hstep := r13.1
  have hparity := r13.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `01001010010100`. -/
theorem parameters_01001010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
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
    : ∃ q : Nat, x0 = 512*q+498 ∧ x1 = 256*q+249 ∧ x2 = 768*q+748 ∧ x3 = 384*q+374 ∧ x4 = 192*q+187 ∧ x5 = 576*q+562 ∧ x6 = 288*q+281 ∧ x7 = 864*q+844 ∧ x8 = 432*q+422 ∧ x9 = 216*q+211 ∧ x10 = 648*q+634 ∧ x11 = 324*q+317 ∧ x12 = 972*q+952 ∧ x13 = 486*q+476 ∧ x14 = 243*q+238 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_0100101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hstep := r13.1
  have hparity := r13.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `01001010010101`. -/
theorem parameters_01001010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
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
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    : ∃ q : Nat, x0 = 512*q+242 ∧ x1 = 256*q+121 ∧ x2 = 768*q+364 ∧ x3 = 384*q+182 ∧ x4 = 192*q+91 ∧ x5 = 576*q+274 ∧ x6 = 288*q+137 ∧ x7 = 864*q+412 ∧ x8 = 432*q+206 ∧ x9 = 216*q+103 ∧ x10 = 648*q+310 ∧ x11 = 324*q+155 ∧ x12 = 972*q+466 ∧ x13 = 486*q+233 ∧ x14 = 1458*q+700 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_0100101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hstep := r13.1
  have hparity := r13.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `01010010100100`. -/
theorem parameters_01010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
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
    : ∃ q : Nat, x0 = 512*q+246 ∧ x1 = 256*q+123 ∧ x2 = 768*q+370 ∧ x3 = 384*q+185 ∧ x4 = 1152*q+556 ∧ x5 = 576*q+278 ∧ x6 = 288*q+139 ∧ x7 = 864*q+418 ∧ x8 = 432*q+209 ∧ x9 = 1296*q+628 ∧ x10 = 648*q+314 ∧ x11 = 324*q+157 ∧ x12 = 972*q+472 ∧ x13 = 486*q+236 ∧ x14 = 243*q+118 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_0101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hstep := r13.1
  have hparity := r13.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `01010010100101`. -/
theorem parameters_01010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
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
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    : ∃ q : Nat, x0 = 512*q+502 ∧ x1 = 256*q+251 ∧ x2 = 768*q+754 ∧ x3 = 384*q+377 ∧ x4 = 1152*q+1132 ∧ x5 = 576*q+566 ∧ x6 = 288*q+283 ∧ x7 = 864*q+850 ∧ x8 = 432*q+425 ∧ x9 = 1296*q+1276 ∧ x10 = 648*q+638 ∧ x11 = 324*q+319 ∧ x12 = 972*q+958 ∧ x13 = 486*q+479 ∧ x14 = 1458*q+1438 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_0101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hstep := r13.1
  have hparity := r13.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `10010100101000`. -/
theorem parameters_10010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
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
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    : ∃ q : Nat, x0 = 512*q+249 ∧ x1 = 1536*q+748 ∧ x2 = 768*q+374 ∧ x3 = 384*q+187 ∧ x4 = 1152*q+562 ∧ x5 = 576*q+281 ∧ x6 = 1728*q+844 ∧ x7 = 864*q+422 ∧ x8 = 432*q+211 ∧ x9 = 1296*q+634 ∧ x10 = 648*q+317 ∧ x11 = 1944*q+952 ∧ x12 = 972*q+476 ∧ x13 = 486*q+238 ∧ x14 = 243*q+119 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_1001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hstep := r13.1
  have hparity := r13.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `10010100101001`. -/
theorem parameters_10010100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
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
    : ∃ q : Nat, x0 = 512*q+505 ∧ x1 = 1536*q+1516 ∧ x2 = 768*q+758 ∧ x3 = 384*q+379 ∧ x4 = 1152*q+1138 ∧ x5 = 576*q+569 ∧ x6 = 1728*q+1708 ∧ x7 = 864*q+854 ∧ x8 = 432*q+427 ∧ x9 = 1296*q+1282 ∧ x10 = 648*q+641 ∧ x11 = 1944*q+1924 ∧ x12 = 972*q+962 ∧ x13 = 486*q+481 ∧ x14 = 1458*q+1444 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_1001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hstep := r13.1
  have hparity := r13.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `0100101001010010`. -/
theorem parameters_0100101001010010
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
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    : ∃ q : Nat, x0 = 1024*q+1010 ∧ x1 = 512*q+505 ∧ x2 = 1536*q+1516 ∧ x3 = 768*q+758 ∧ x4 = 384*q+379 ∧ x5 = 1152*q+1138 ∧ x6 = 576*q+569 ∧ x7 = 1728*q+1708 ∧ x8 = 864*q+854 ∧ x9 = 432*q+427 ∧ x10 = 1296*q+1282 ∧ x11 = 648*q+641 ∧ x12 = 1944*q+1924 ∧ x13 = 972*q+962 ∧ x14 = 486*q+481 ∧ x15 = 1458*q+1444 ∧ x16 = 729*q+722 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_010010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hstep := r15.1
  have hparity := r15.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1001010010100100`. -/
theorem parameters_1001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
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
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    : ∃ q : Nat, x0 = 1024*q+505 ∧ x1 = 3072*q+1516 ∧ x2 = 1536*q+758 ∧ x3 = 768*q+379 ∧ x4 = 2304*q+1138 ∧ x5 = 1152*q+569 ∧ x6 = 3456*q+1708 ∧ x7 = 1728*q+854 ∧ x8 = 864*q+427 ∧ x9 = 2592*q+1282 ∧ x10 = 1296*q+641 ∧ x11 = 3888*q+1924 ∧ x12 = 1944*q+962 ∧ x13 = 972*q+481 ∧ x14 = 2916*q+1444 ∧ x15 = 1458*q+722 ∧ x16 = 729*q+361 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hstep := r15.1
  have hparity := r15.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `1001010010100101`. -/
theorem parameters_1001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
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
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    : ∃ q : Nat, x0 = 1024*q+1017 ∧ x1 = 3072*q+3052 ∧ x2 = 1536*q+1526 ∧ x3 = 768*q+763 ∧ x4 = 2304*q+2290 ∧ x5 = 1152*q+1145 ∧ x6 = 3456*q+3436 ∧ x7 = 1728*q+1718 ∧ x8 = 864*q+859 ∧ x9 = 2592*q+2578 ∧ x10 = 1296*q+1289 ∧ x11 = 3888*q+3868 ∧ x12 = 1944*q+1934 ∧ x13 = 972*q+967 ∧ x14 = 2916*q+2902 ∧ x15 = 1458*q+1451 ∧ x16 = 4374*q+4354 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hstep := r15.1
  have hparity := r15.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `01001010010100100`. -/
theorem parameters_01001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : Nat)
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
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    : ∃ q : Nat, x0 = 2048*q+1010 ∧ x1 = 1024*q+505 ∧ x2 = 3072*q+1516 ∧ x3 = 1536*q+758 ∧ x4 = 768*q+379 ∧ x5 = 2304*q+1138 ∧ x6 = 1152*q+569 ∧ x7 = 3456*q+1708 ∧ x8 = 1728*q+854 ∧ x9 = 864*q+427 ∧ x10 = 2592*q+1282 ∧ x11 = 1296*q+641 ∧ x12 = 3888*q+1924 ∧ x13 = 1944*q+962 ∧ x14 = 972*q+481 ∧ x15 = 2916*q+1444 ∧ x16 = 1458*q+722 ∧ x17 = 729*q+361 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16⟩ := parameters_0100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  have hstep := r16.1
  have hparity := r16.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
  have hq : q = 2*(q/2)+0 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Exact source residue and full affine trace for branch `01001010010100101`. -/
theorem parameters_01001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : Nat)
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
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    : ∃ q : Nat, x0 = 2048*q+2034 ∧ x1 = 1024*q+1017 ∧ x2 = 3072*q+3052 ∧ x3 = 1536*q+1526 ∧ x4 = 768*q+763 ∧ x5 = 2304*q+2290 ∧ x6 = 1152*q+1145 ∧ x7 = 3456*q+3436 ∧ x8 = 1728*q+1718 ∧ x9 = 864*q+859 ∧ x10 = 2592*q+2578 ∧ x11 = 1296*q+1289 ∧ x12 = 3888*q+3868 ∧ x13 = 1944*q+1934 ∧ x14 = 972*q+967 ∧ x15 = 2916*q+2902 ∧ x16 = 1458*q+1451 ∧ x17 = 4374*q+4354 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16⟩ := parameters_0100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  have hstep := r16.1
  have hparity := r16.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
  have hq : q = 2*(q/2)+1 := by omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Terminal branch `000` cannot satisfy the band bounds. -/
theorem exclude_000
    (x0 x1 x2 x3 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 4*x0 ≤ 21*b)
    (h3 : b ≤ x3 ∧ 4*x3 ≤ 21*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3⟩ := parameters_000 x0 x1 x2 x3 r0 r1 r2
  clear r0 r1 r2
  omega

/-- Terminal branch `001000` cannot satisfy the band bounds. -/
theorem exclude_001000
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 4*x0 ≤ 21*b)
    (h6 : b ≤ x6 ∧ 4*x6 ≤ 21*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_001000 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  clear r0 r1 r2 r3 r4 r5
  omega

/-- Terminal branch `00100100` cannot satisfy the band bounds. -/
theorem exclude_00100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 4*x0 ≤ 21*b)
    (h8 : b ≤ x8 ∧ 4*x8 ≤ 21*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_00100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  clear r0 r1 r2 r3 r4 r5 r6 r7
  omega

/-- Terminal branch `0010010100` cannot satisfy the band bounds. -/
theorem exclude_0010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 4*x0 ≤ 21*b)
    (h5 : b ≤ x5 ∧ 4*x5 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  omega

/-- Terminal branch `0010010101` cannot satisfy the band bounds. -/
theorem exclude_0010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (b : Nat) (hb : 1 < b)
    (h5 : b ≤ x5 ∧ 4*x5 ≤ 21*b)
    (h10 : b ≤ x10 ∧ 4*x10 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  omega

/-- Terminal branch `001001011` cannot satisfy the band bounds. -/
theorem exclude_001001011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_00100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  omega

/-- Terminal branch `0010011` cannot satisfy the band bounds. -/
theorem exclude_0010011
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_001001 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  omega

/-- Terminal branch `00101000` cannot satisfy the band bounds. -/
theorem exclude_00101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 4*x0 ≤ 21*b)
    (h8 : b ≤ x8 ∧ 4*x8 ≤ 21*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_00101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  clear r0 r1 r2 r3 r4 r5 r6 r7
  omega

/-- Terminal branch `00101001000` cannot satisfy the band bounds. -/
theorem exclude_00101001000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 4*x0 ≤ 21*b)
    (h11 : b ≤ x11 ∧ 4*x11 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_00101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  omega

/-- Terminal branch `00101001001` cannot satisfy the band bounds. -/
theorem exclude_00101001001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
    (b : Nat) (hb : 1 < b)
    (h5 : b ≤ x5 ∧ 4*x5 ≤ 21*b)
    (h10 : b ≤ x10 ∧ 4*x10 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_00101001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  omega

/-- Terminal branch `0010100101000` cannot satisfy the band bounds. -/
theorem exclude_0010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 4*x0 ≤ 21*b)
    (h13 : b ≤ x13 ∧ 4*x13 ≤ 21*b)
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
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_0010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  omega

/-- Terminal branch `001010010100100` cannot satisfy the band bounds. -/
theorem exclude_001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (b : Nat) (hb : 1 < b)
    (h10 : b ≤ x10 ∧ 4*x10 ≤ 21*b)
    (h15 : b ≤ x15 ∧ 4*x15 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  omega

/-- Terminal branch `001010010100101` cannot satisfy the band bounds. -/
theorem exclude_001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (b : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ 4*x2 ≤ 21*b)
    (h15 : b ≤ x15 ∧ 4*x15 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  omega

/-- Terminal branch `00101001010011` cannot satisfy the band bounds. -/
theorem exclude_00101001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
    (b : Nat) (hb : 1 < b)
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
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_0010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hparity := r13.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  omega

/-- Terminal branch `001010010101` cannot satisfy the band bounds. -/
theorem exclude_001010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
    (b : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ 4*x2 ≤ 21*b)
    (h12 : b ≤ x12 ∧ 4*x12 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  omega

/-- Terminal branch `00101001011` cannot satisfy the band bounds. -/
theorem exclude_00101001011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
    (b : Nat) (hb : 1 < b)
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
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  omega

/-- Terminal branch `001010011` cannot satisfy the band bounds. -/
theorem exclude_001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_00101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  omega

/-- Terminal branch `0010101` cannot satisfy the band bounds. -/
theorem exclude_0010101
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (b : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ 4*x2 ≤ 21*b)
    (h7 : b ≤ x7 ∧ 4*x7 ≤ 21*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_0010101 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  clear r0 r1 r2 r3 r4 r5 r6
  omega

/-- Terminal branch `001011` cannot satisfy the band bounds. -/
theorem exclude_001011
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_00101 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  have hparity := r5.2
  clear r0 r1 r2 r3 r4 r5
  omega

/-- Terminal branch `0011` cannot satisfy the band bounds. -/
theorem exclude_0011
    (x0 x1 x2 x3 x4 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3⟩ := parameters_001 x0 x1 x2 x3 r0 r1 r2
  have hparity := r3.2
  clear r0 r1 r2 r3
  omega

/-- Terminal branch `01000` cannot satisfy the band bounds. -/
theorem exclude_01000
    (x0 x1 x2 x3 x4 x5 : Nat)
    (b : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ 4*x2 ≤ 21*b)
    (h5 : b ≤ x5 ∧ 4*x5 ≤ 21*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_01000 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  clear r0 r1 r2 r3 r4
  omega

/-- Terminal branch `01001000` cannot satisfy the band bounds. -/
theorem exclude_01001000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 4*x0 ≤ 21*b)
    (h8 : b ≤ x8 ∧ 4*x8 ≤ 21*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_01001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  clear r0 r1 r2 r3 r4 r5 r6 r7
  omega

/-- Terminal branch `01001001` cannot satisfy the band bounds. -/
theorem exclude_01001001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (b : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ 4*x2 ≤ 21*b)
    (h7 : b ≤ x7 ∧ 4*x7 ≤ 21*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_01001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  clear r0 r1 r2 r3 r4 r5 r6 r7
  omega

/-- Terminal branch `0100101000` cannot satisfy the band bounds. -/
theorem exclude_0100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (b : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ 4*x2 ≤ 21*b)
    (h10 : b ≤ x10 ∧ 4*x10 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  omega

/-- Terminal branch `010010100100` cannot satisfy the band bounds. -/
theorem exclude_010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
    (b : Nat) (hb : 1 < b)
    (h7 : b ≤ x7 ∧ 4*x7 ≤ 21*b)
    (h12 : b ≤ x12 ∧ 4*x12 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  omega

/-- Terminal branch `010010100101000` cannot satisfy the band bounds. -/
theorem exclude_010010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (b : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ 4*x2 ≤ 21*b)
    (h15 : b ≤ x15 ∧ 4*x15 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  omega

/-- Terminal branch `01001010010100100` cannot satisfy the band bounds. -/
theorem exclude_01001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : Nat)
    (b : Nat) (hb : 1 < b)
    (h12 : b ≤ x12 ∧ 4*x12 ≤ 21*b)
    (h17 : b ≤ x17 ∧ 4*x17 ≤ 21*b)
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
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17⟩ := parameters_01001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
  omega

/-- Terminal branch `01001010010100101` cannot satisfy the band bounds. -/
theorem exclude_01001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : Nat)
    (b : Nat) (hb : 1 < b)
    (h4 : b ≤ x4 ∧ 4*x4 ≤ 21*b)
    (h17 : b ≤ x17 ∧ 4*x17 ≤ 21*b)
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
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17⟩ := parameters_01001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
  omega

/-- Terminal branch `0100101001010011` cannot satisfy the band bounds. -/
theorem exclude_0100101001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
    (b : Nat) (hb : 1 < b)
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
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩ := parameters_010010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  have hparity := r15.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  omega

/-- Terminal branch `01001010010101` cannot satisfy the band bounds. -/
theorem exclude_01001010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 4*x1 ≤ 21*b)
    (h14 : b ≤ x14 ∧ 4*x14 ≤ 21*b)
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
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_01001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  omega

/-- Terminal branch `0100101001011` cannot satisfy the band bounds. -/
theorem exclude_0100101001011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
    (b : Nat) (hb : 1 < b)
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
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hparity := r12.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  omega

/-- Terminal branch `01001010011` cannot satisfy the band bounds. -/
theorem exclude_01001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
    (b : Nat) (hb : 1 < b)
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
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hparity := r10.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  omega

/-- Terminal branch `010010101` cannot satisfy the band bounds. -/
theorem exclude_010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (b : Nat) (hb : 1 < b)
    (h4 : b ≤ x4 ∧ 4*x4 ≤ 21*b)
    (h9 : b ≤ x9 ∧ 4*x9 ≤ 21*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  omega

/-- Terminal branch `01001011` cannot satisfy the band bounds. -/
theorem exclude_01001011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_0100101 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  omega

/-- Terminal branch `010011` cannot satisfy the band bounds. -/
theorem exclude_010011
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_01001 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  have hparity := r5.2
  clear r0 r1 r2 r3 r4 r5
  omega

/-- Terminal branch `0101000` cannot satisfy the band bounds. -/
theorem exclude_0101000
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (b : Nat) (hb : 1 < b)
    (h4 : b ≤ x4 ∧ 4*x4 ≤ 21*b)
    (h7 : b ≤ x7 ∧ 4*x7 ≤ 21*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_0101000 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  clear r0 r1 r2 r3 r4 r5 r6
  omega

/-- Terminal branch `0101001000` cannot satisfy the band bounds. -/
theorem exclude_0101001000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (b : Nat) (hb : 1 < b)
    (h2 : b ≤ x2 ∧ 4*x2 ≤ 21*b)
    (h10 : b ≤ x10 ∧ 4*x10 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  omega

/-- Terminal branch `0101001001` cannot satisfy the band bounds. -/
theorem exclude_0101001001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (b : Nat) (hb : 1 < b)
    (h4 : b ≤ x4 ∧ 4*x4 ≤ 21*b)
    (h9 : b ≤ x9 ∧ 4*x9 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_0101001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  omega

/-- Terminal branch `010100101000` cannot satisfy the band bounds. -/
theorem exclude_010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
    (b : Nat) (hb : 1 < b)
    (h4 : b ≤ x4 ∧ 4*x4 ≤ 21*b)
    (h12 : b ≤ x12 ∧ 4*x12 ≤ 21*b)
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
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  omega

/-- Terminal branch `01010010100100` cannot satisfy the band bounds. -/
theorem exclude_01010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
    (b : Nat) (hb : 1 < b)
    (h9 : b ≤ x9 ∧ 4*x9 ≤ 21*b)
    (h14 : b ≤ x14 ∧ 4*x14 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_01010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  omega

/-- Terminal branch `01010010100101` cannot satisfy the band bounds. -/
theorem exclude_01010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 4*x1 ≤ 21*b)
    (h14 : b ≤ x14 ∧ 4*x14 ≤ 21*b)
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
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_01010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  omega

/-- Terminal branch `0101001010011` cannot satisfy the band bounds. -/
theorem exclude_0101001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
    (b : Nat) (hb : 1 < b)
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
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := parameters_010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hparity := r12.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  omega

/-- Terminal branch `01010010101` cannot satisfy the band bounds. -/
theorem exclude_01010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 4*x1 ≤ 21*b)
    (h11 : b ≤ x11 ∧ 4*x11 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_01010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  omega

/-- Terminal branch `0101001011` cannot satisfy the band bounds. -/
theorem exclude_0101001011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hparity := r9.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  omega

/-- Terminal branch `01010011` cannot satisfy the band bounds. -/
theorem exclude_01010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_0101001 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  have hparity := r7.2
  clear r0 r1 r2 r3 r4 r5 r6 r7
  omega

/-- Terminal branch `010101` cannot satisfy the band bounds. -/
theorem exclude_010101
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 4*x1 ≤ 21*b)
    (h6 : b ≤ x6 ∧ 4*x6 ≤ 21*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_010101 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  clear r0 r1 r2 r3 r4 r5
  omega

/-- Terminal branch `01011` cannot satisfy the band bounds. -/
theorem exclude_01011
    (x0 x1 x2 x3 x4 x5 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4⟩ := parameters_0101 x0 x1 x2 x3 x4 r0 r1 r2 r3
  have hparity := r4.2
  clear r0 r1 r2 r3 r4
  omega

/-- Terminal branch `011` cannot satisfy the band bounds. -/
theorem exclude_011
    (x0 x1 x2 x3 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2⟩ := parameters_01 x0 x1 x2 r0 r1
  have hparity := r2.2
  clear r0 r1 r2
  omega

/-- Terminal branch `1000` cannot satisfy the band bounds. -/
theorem exclude_1000
    (x0 x1 x2 x3 x4 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 4*x1 ≤ 21*b)
    (h4 : b ≤ x4 ∧ 4*x4 ≤ 21*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4⟩ := parameters_1000 x0 x1 x2 x3 x4 r0 r1 r2 r3
  clear r0 r1 r2 r3
  omega

/-- Terminal branch `1001000` cannot satisfy the band bounds. -/
theorem exclude_1001000
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 4*x1 ≤ 21*b)
    (h7 : b ≤ x7 ∧ 4*x7 ≤ 21*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_1001000 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  clear r0 r1 r2 r3 r4 r5 r6
  omega

/-- Terminal branch `1001001` cannot satisfy the band bounds. -/
theorem exclude_1001001
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 4*x1 ≤ 21*b)
    (h6 : b ≤ x6 ∧ 4*x6 ≤ 21*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7⟩ := parameters_1001001 x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6
  clear r0 r1 r2 r3 r4 r5 r6
  omega

/-- Terminal branch `100101000` cannot satisfy the band bounds. -/
theorem exclude_100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 4*x1 ≤ 21*b)
    (h9 : b ≤ x9 ∧ 4*x9 ≤ 21*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  omega

/-- Terminal branch `10010100100` cannot satisfy the band bounds. -/
theorem exclude_10010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
    (b : Nat) (hb : 1 < b)
    (h6 : b ≤ x6 ∧ 4*x6 ≤ 21*b)
    (h11 : b ≤ x11 ∧ 4*x11 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_10010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  omega

/-- Terminal branch `10010100101000` cannot satisfy the band bounds. -/
theorem exclude_10010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 4*x1 ≤ 21*b)
    (h14 : b ≤ x14 ∧ 4*x14 ≤ 21*b)
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
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_10010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  omega

/-- Terminal branch `1001010010100100` cannot satisfy the band bounds. -/
theorem exclude_1001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
    (b : Nat) (hb : 1 < b)
    (h11 : b ≤ x11 ∧ 4*x11 ≤ 21*b)
    (h16 : b ≤ x16 ∧ 4*x16 ≤ 21*b)
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
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16⟩ := parameters_1001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  omega

/-- Terminal branch `1001010010100101` cannot satisfy the band bounds. -/
theorem exclude_1001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 4*x3 ≤ 21*b)
    (h16 : b ≤ x16 ∧ 4*x16 ≤ 21*b)
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
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16⟩ := parameters_1001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  omega

/-- Terminal branch `100101001010011` cannot satisfy the band bounds. -/
theorem exclude_100101001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (b : Nat) (hb : 1 < b)
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
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14⟩ := parameters_10010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
  have hparity := r14.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
  omega

/-- Terminal branch `1001010010101` cannot satisfy the band bounds. -/
theorem exclude_1001010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 4*x0 ≤ 21*b)
    (h13 : b ≤ x13 ∧ 4*x13 ≤ 21*b)
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
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_1001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  omega

/-- Terminal branch `100101001011` cannot satisfy the band bounds. -/
theorem exclude_100101001011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
    (b : Nat) (hb : 1 < b)
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
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_10010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  omega

/-- Terminal branch `1001010011` cannot satisfy the band bounds. -/
theorem exclude_1001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  have hparity := r9.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  omega

/-- Terminal branch `10010101` cannot satisfy the band bounds. -/
theorem exclude_10010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 4*x3 ≤ 21*b)
    (h8 : b ≤ x8 ∧ 4*x8 ≤ 21*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_10010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  clear r0 r1 r2 r3 r4 r5 r6 r7
  omega

/-- Terminal branch `1001011` cannot satisfy the band bounds. -/
theorem exclude_1001011
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_100101 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  omega

/-- Terminal branch `10011` cannot satisfy the band bounds. -/
theorem exclude_10011
    (x0 x1 x2 x3 x4 x5 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4⟩ := parameters_1001 x0 x1 x2 x3 x4 r0 r1 r2 r3
  have hparity := r4.2
  clear r0 r1 r2 r3 r4
  omega

/-- Terminal branch `101000` cannot satisfy the band bounds. -/
theorem exclude_101000
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 4*x3 ≤ 21*b)
    (h6 : b ≤ x6 ∧ 4*x6 ≤ 21*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_101000 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  clear r0 r1 r2 r3 r4 r5
  omega

/-- Terminal branch `101001000` cannot satisfy the band bounds. -/
theorem exclude_101001000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (b : Nat) (hb : 1 < b)
    (h1 : b ≤ x1 ∧ 4*x1 ≤ 21*b)
    (h9 : b ≤ x9 ∧ 4*x9 ≤ 21*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  omega

/-- Terminal branch `101001001` cannot satisfy the band bounds. -/
theorem exclude_101001001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 4*x3 ≤ 21*b)
    (h8 : b ≤ x8 ∧ 4*x8 ≤ 21*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := parameters_101001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r0 r1 r2 r3 r4 r5 r6 r7 r8
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  omega

/-- Terminal branch `10100101000` cannot satisfy the band bounds. -/
theorem exclude_10100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
    (b : Nat) (hb : 1 < b)
    (h3 : b ≤ x3 ∧ 4*x3 ≤ 21*b)
    (h11 : b ≤ x11 ∧ 4*x11 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_10100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  omega

/-- Terminal branch `1010010100100` cannot satisfy the band bounds. -/
theorem exclude_1010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
    (b : Nat) (hb : 1 < b)
    (h8 : b ≤ x8 ∧ 4*x8 ≤ 21*b)
    (h13 : b ≤ x13 ∧ 4*x13 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_1010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  omega

/-- Terminal branch `1010010100101` cannot satisfy the band bounds. -/
theorem exclude_1010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 4*x0 ≤ 21*b)
    (h13 : b ≤ x13 ∧ 4*x13 ≤ 21*b)
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
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_1010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  omega

/-- Terminal branch `101001010011` cannot satisfy the band bounds. -/
theorem exclude_101001010011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Nat)
    (b : Nat) (hb : 1 < b)
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
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_10100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  have hparity := r11.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  omega

/-- Terminal branch `1010010101` cannot satisfy the band bounds. -/
theorem exclude_1010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 4*x0 ≤ 21*b)
    (h10 : b ≤ x10 ∧ 4*x10 ≤ 21*b)
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩ := parameters_1010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  omega

/-- Terminal branch `101001011` cannot satisfy the band bounds. -/
theorem exclude_101001011
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_10100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  have hparity := r8.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8
  omega

/-- Terminal branch `1010011` cannot satisfy the band bounds. -/
theorem exclude_1010011
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_101001 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  have hparity := r6.2
  clear r0 r1 r2 r3 r4 r5 r6
  omega

/-- Terminal branch `10101` cannot satisfy the band bounds. -/
theorem exclude_10101
    (x0 x1 x2 x3 x4 x5 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 4*x0 ≤ 21*b)
    (h5 : b ≤ x5 ∧ 4*x5 ≤ 21*b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5⟩ := parameters_10101 x0 x1 x2 x3 x4 x5 r0 r1 r2 r3 r4
  clear r0 r1 r2 r3 r4
  omega

/-- Terminal branch `1011` cannot satisfy the band bounds. -/
theorem exclude_1011
    (x0 x1 x2 x3 x4 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    : False := by
  obtain ⟨q,p0,p1,p2,p3⟩ := parameters_101 x0 x1 x2 x3 r0 r1 r2
  have hparity := r3.2
  clear r0 r1 r2 r3
  omega

/-- Terminal branch `11` cannot satisfy the band bounds. -/
theorem exclude_11
    (x0 x1 x2 : Nat)
    (b : Nat) (hb : 1 < b)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    : False := by
  obtain ⟨q,p0,p1⟩ := parameters_1 x0 x1 r0
  have hparity := r1.2
  clear r0 r1
  omega

theorem impossible_trace
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 4*x0 ≤ 21*b)
    (h1 : b ≤ x1 ∧ 4*x1 ≤ 21*b)
    (h2 : b ≤ x2 ∧ 4*x2 ≤ 21*b)
    (h3 : b ≤ x3 ∧ 4*x3 ≤ 21*b)
    (h4 : b ≤ x4 ∧ 4*x4 ≤ 21*b)
    (h5 : b ≤ x5 ∧ 4*x5 ≤ 21*b)
    (h6 : b ≤ x6 ∧ 4*x6 ≤ 21*b)
    (h7 : b ≤ x7 ∧ 4*x7 ≤ 21*b)
    (h8 : b ≤ x8 ∧ 4*x8 ≤ 21*b)
    (h9 : b ≤ x9 ∧ 4*x9 ≤ 21*b)
    (h10 : b ≤ x10 ∧ 4*x10 ≤ 21*b)
    (h11 : b ≤ x11 ∧ 4*x11 ≤ 21*b)
    (h12 : b ≤ x12 ∧ 4*x12 ≤ 21*b)
    (h13 : b ≤ x13 ∧ 4*x13 ≤ 21*b)
    (h14 : b ≤ x14 ∧ 4*x14 ≤ 21*b)
    (h15 : b ≤ x15 ∧ 4*x15 ≤ 21*b)
    (h16 : b ≤ x16 ∧ 4*x16 ≤ 21*b)
    (h17 : b ≤ x17 ∧ 4*x17 ≤ 21*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0) ∨ (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0) ∨ (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0) ∨ (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0) ∨ (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0) ∨ (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0) ∨ (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0) ∨ (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0) ∨ (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0) ∨ (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0) ∨ (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0) ∨ (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0) ∨ (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0) ∨ (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0) ∨ (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0) ∨ (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0) ∨ (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0) ∨ (x17 = 3*x16+1 ∧ x16%2 = 1))
    : False := by
  revert r16 r15 r14 r13 r12 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0
  intro r0
  rcases r0 with r0 | r0
  · -- branch 0 at time 0
    intro r1
    rcases r1 with r1 | r1
    · -- branch 0 at time 1
      intro r2
      rcases r2 with r2 | r2
      · -- branch 0 at time 2
        exact False.elim (exclude_000 x0 x1 x2 x3 b hb h0 h3 r0 r1 r2)
      · -- branch 1 at time 2
        intro r3
        rcases r3 with r3 | r3
        · -- branch 0 at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- branch 0 at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- branch 0 at time 5
              exact False.elim (exclude_001000 x0 x1 x2 x3 x4 x5 x6 b hb h0 h6 r0 r1 r2 r3 r4 r5)
            · -- branch 1 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  exact False.elim (exclude_00100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
                · -- branch 1 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      exact False.elim (exclude_0010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb h0 h5 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                    · -- branch 1 at time 9
                      exact False.elim (exclude_0010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb h5 h10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                  · -- branch 1 at time 8
                    exact False.elim (exclude_001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8)
              · -- branch 1 at time 6
                exact False.elim (exclude_0010011 x0 x1 x2 x3 x4 x5 x6 x7 b hb r0 r1 r2 r3 r4 r5 r6)
          · -- branch 1 at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- branch 0 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  exact False.elim (exclude_00101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
                · -- branch 1 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        exact False.elim (exclude_00101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb h0 h11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                      · -- branch 1 at time 10
                        exact False.elim (exclude_00101001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb h5 h10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                    · -- branch 1 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            exact False.elim (exclude_0010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb h0 h13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                          · -- branch 1 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                exact False.elim (exclude_001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb h10 h15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                              · -- branch 1 at time 14
                                exact False.elim (exclude_001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb h2 h15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                            · -- branch 1 at time 13
                              exact False.elim (exclude_00101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                        · -- branch 1 at time 11
                          exact False.elim (exclude_001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb h2 h12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                      · -- branch 1 at time 10
                        exact False.elim (exclude_00101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                  · -- branch 1 at time 8
                    exact False.elim (exclude_001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8)
              · -- branch 1 at time 6
                exact False.elim (exclude_0010101 x0 x1 x2 x3 x4 x5 x6 x7 b hb h2 h7 r0 r1 r2 r3 r4 r5 r6)
            · -- branch 1 at time 5
              exact False.elim (exclude_001011 x0 x1 x2 x3 x4 x5 x6 b hb r0 r1 r2 r3 r4 r5)
        · -- branch 1 at time 3
          exact False.elim (exclude_0011 x0 x1 x2 x3 x4 b hb r0 r1 r2 r3)
    · -- branch 1 at time 1
      intro r2
      rcases r2 with r2 | r2
      · -- branch 0 at time 2
        intro r3
        rcases r3 with r3 | r3
        · -- branch 0 at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- branch 0 at time 4
            exact False.elim (exclude_01000 x0 x1 x2 x3 x4 x5 b hb h2 h5 r0 r1 r2 r3 r4)
          · -- branch 1 at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- branch 0 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  exact False.elim (exclude_01001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
                · -- branch 1 at time 7
                  exact False.elim (exclude_01001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb h2 h7 r0 r1 r2 r3 r4 r5 r6 r7)
              · -- branch 1 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      exact False.elim (exclude_0100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb h2 h10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                    · -- branch 1 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          exact False.elim (exclude_010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb h7 h12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                        · -- branch 1 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                exact False.elim (exclude_010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb h2 h15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                              · -- branch 1 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    exact False.elim (exclude_01001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb h12 h17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                                  · -- branch 1 at time 16
                                    exact False.elim (exclude_01001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb h4 h17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                                · -- branch 1 at time 15
                                  exact False.elim (exclude_0100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                            · -- branch 1 at time 13
                              exact False.elim (exclude_01001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb h1 h14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                          · -- branch 1 at time 12
                            exact False.elim (exclude_0100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                      · -- branch 1 at time 10
                        exact False.elim (exclude_01001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                  · -- branch 1 at time 8
                    exact False.elim (exclude_010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb h4 h9 r0 r1 r2 r3 r4 r5 r6 r7 r8)
                · -- branch 1 at time 7
                  exact False.elim (exclude_01001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb r0 r1 r2 r3 r4 r5 r6 r7)
            · -- branch 1 at time 5
              exact False.elim (exclude_010011 x0 x1 x2 x3 x4 x5 x6 b hb r0 r1 r2 r3 r4 r5)
        · -- branch 1 at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- branch 0 at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- branch 0 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                exact False.elim (exclude_0101000 x0 x1 x2 x3 x4 x5 x6 x7 b hb h4 h7 r0 r1 r2 r3 r4 r5 r6)
              · -- branch 1 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      exact False.elim (exclude_0101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb h2 h10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                    · -- branch 1 at time 9
                      exact False.elim (exclude_0101001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb h4 h9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                  · -- branch 1 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          exact False.elim (exclude_010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb h4 h12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                        · -- branch 1 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              exact False.elim (exclude_01010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb h9 h14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                            · -- branch 1 at time 13
                              exact False.elim (exclude_01010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb h1 h14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                          · -- branch 1 at time 12
                            exact False.elim (exclude_0101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                      · -- branch 1 at time 10
                        exact False.elim (exclude_01010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb h1 h11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                    · -- branch 1 at time 9
                      exact False.elim (exclude_0101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                · -- branch 1 at time 7
                  exact False.elim (exclude_01010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb r0 r1 r2 r3 r4 r5 r6 r7)
            · -- branch 1 at time 5
              exact False.elim (exclude_010101 x0 x1 x2 x3 x4 x5 x6 b hb h1 h6 r0 r1 r2 r3 r4 r5)
          · -- branch 1 at time 4
            exact False.elim (exclude_01011 x0 x1 x2 x3 x4 x5 b hb r0 r1 r2 r3 r4)
      · -- branch 1 at time 2
        exact False.elim (exclude_011 x0 x1 x2 x3 b hb r0 r1 r2)
  · -- branch 1 at time 0
    intro r1
    rcases r1 with r1 | r1
    · -- branch 0 at time 1
      intro r2
      rcases r2 with r2 | r2
      · -- branch 0 at time 2
        intro r3
        rcases r3 with r3 | r3
        · -- branch 0 at time 3
          exact False.elim (exclude_1000 x0 x1 x2 x3 x4 b hb h1 h4 r0 r1 r2 r3)
        · -- branch 1 at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- branch 0 at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- branch 0 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                exact False.elim (exclude_1001000 x0 x1 x2 x3 x4 x5 x6 x7 b hb h1 h7 r0 r1 r2 r3 r4 r5 r6)
              · -- branch 1 at time 6
                exact False.elim (exclude_1001001 x0 x1 x2 x3 x4 x5 x6 x7 b hb h1 h6 r0 r1 r2 r3 r4 r5 r6)
            · -- branch 1 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    exact False.elim (exclude_100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb h1 h9 r0 r1 r2 r3 r4 r5 r6 r7 r8)
                  · -- branch 1 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        exact False.elim (exclude_10010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb h6 h11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                      · -- branch 1 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              exact False.elim (exclude_10010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb h1 h14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                            · -- branch 1 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  exact False.elim (exclude_1001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb h11 h16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                                · -- branch 1 at time 15
                                  exact False.elim (exclude_1001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb h3 h16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                              · -- branch 1 at time 14
                                exact False.elim (exclude_100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                          · -- branch 1 at time 12
                            exact False.elim (exclude_1001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb h0 h13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                        · -- branch 1 at time 11
                          exact False.elim (exclude_100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                    · -- branch 1 at time 9
                      exact False.elim (exclude_1001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                · -- branch 1 at time 7
                  exact False.elim (exclude_10010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb h3 h8 r0 r1 r2 r3 r4 r5 r6 r7)
              · -- branch 1 at time 6
                exact False.elim (exclude_1001011 x0 x1 x2 x3 x4 x5 x6 x7 b hb r0 r1 r2 r3 r4 r5 r6)
          · -- branch 1 at time 4
            exact False.elim (exclude_10011 x0 x1 x2 x3 x4 x5 b hb r0 r1 r2 r3 r4)
      · -- branch 1 at time 2
        intro r3
        rcases r3 with r3 | r3
        · -- branch 0 at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- branch 0 at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- branch 0 at time 5
              exact False.elim (exclude_101000 x0 x1 x2 x3 x4 x5 x6 b hb h3 h6 r0 r1 r2 r3 r4 r5)
            · -- branch 1 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    exact False.elim (exclude_101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb h1 h9 r0 r1 r2 r3 r4 r5 r6 r7 r8)
                  · -- branch 1 at time 8
                    exact False.elim (exclude_101001001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb h3 h8 r0 r1 r2 r3 r4 r5 r6 r7 r8)
                · -- branch 1 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        exact False.elim (exclude_10100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb h3 h11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                      · -- branch 1 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            exact False.elim (exclude_1010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb h8 h13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                          · -- branch 1 at time 12
                            exact False.elim (exclude_1010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb h0 h13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                        · -- branch 1 at time 11
                          exact False.elim (exclude_101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                    · -- branch 1 at time 9
                      exact False.elim (exclude_1010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb h0 h10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                  · -- branch 1 at time 8
                    exact False.elim (exclude_101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8)
              · -- branch 1 at time 6
                exact False.elim (exclude_1010011 x0 x1 x2 x3 x4 x5 x6 x7 b hb r0 r1 r2 r3 r4 r5 r6)
          · -- branch 1 at time 4
            exact False.elim (exclude_10101 x0 x1 x2 x3 x4 x5 b hb h0 h5 r0 r1 r2 r3 r4)
        · -- branch 1 at time 3
          exact False.elim (exclude_1011 x0 x1 x2 x3 x4 b hb r0 r1 r2 r3)
    · -- branch 1 at time 1
      exact False.elim (exclude_11 x0 x1 x2 b hb r0 r1)

end Collatz.Exploration.WiderBandArithmetic
