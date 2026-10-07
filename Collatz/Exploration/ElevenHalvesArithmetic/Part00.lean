import Collatz.Basic

namespace Collatz.Exploration.ElevenHalvesArithmetic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- Lift one affine identity across a source residue refinement. -/
theorem lift_affine {x q a c e : Nat} (hx : x = a*q+c)
    (hq : q = 2*(q/2)+e) : x = (2*a)*(q/2)+(a*e+c) := by
  calc
    x = a*q+c := hx
    _ = a*(2*(q/2)+e)+c := congrArg (fun u => a*u+c) hq
    _ = (2*a)*(q/2)+(a*e+c) := by
      simp only [Nat.mul_add]
      ac_rfl

/-- Exact source residue and full affine trace for branch `0`. -/
theorem parameters_0
    (x0 x1 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    : ∃ q : Nat, x0 = 2*q+0 ∧ x1 = 1*q+0 := by
  let q := x0
  have p0 : x0 = 1*q+0 := by omega
  have hstep := r0.1
  have hparity := r0.2
  clear r0
  have hq : q = 2*(q/2)+0 := by
    clear hstep
    omega
  clear hparity
  refine ⟨q/2,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · omega

/-- Exact source residue and full affine trace for branch `1`. -/
theorem parameters_1
    (x0 x1 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    : ∃ q : Nat, x0 = 2*q+1 ∧ x1 = 6*q+4 := by
  let q := x0
  have p0 : x0 = 1*q+0 := by omega
  have hstep := r0.1
  have hparity := r0.2
  clear r0
  have hq : q = 2*(q/2)+1 := by
    clear hstep
    omega
  clear hparity
  refine ⟨q/2,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · clear p0
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · clear p0
    omega

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
  refine ⟨q,?_,?_,?_⟩
  · exact p0
  · exact p1
  · clear p0
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · clear p0 p1
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · clear p0 p1
    omega

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
  refine ⟨q,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · clear p0 p1
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · clear p0 p1
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · clear p0 p1
    omega

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
  refine ⟨q,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · clear p0 p1 p2
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · clear p0 p1 p2
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · clear p0 p1 p2
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · clear p0 p1 p2
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · clear p0 p1 p2
    omega

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
  refine ⟨q,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · clear p0 p1 p2
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · clear p0 p1 p2 p3
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · clear p0 p1 p2 p3
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · clear p0 p1 p2 p3
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · clear p0 p1 p2 p3
    omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · clear p0 p1 p2 p3
    omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · clear p0 p1 p2 p3
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · clear p0 p1 p2 p3
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · clear p0 p1 p2 p3
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · clear p0 p1 p2 p3 p4
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · clear p0 p1 p2 p3 p4
    omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · clear p0 p1 p2 p3 p4
    omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · clear p0 p1 p2 p3 p4
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · clear p0 p1 p2 p3 p4
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · clear p0 p1 p2 p3 p4
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · clear p0 p1 p2 p3 p4
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · clear p0 p1 p2 p3 p4
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · clear p0 p1 p2 p3 p4
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · clear p0 p1 p2 p3 p4
    omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · clear p0 p1 p2 p3 p4 p5
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · clear p0 p1 p2 p3 p4 p5
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · clear p0 p1 p2 p3 p4 p5
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · clear p0 p1 p2 p3 p4 p5
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · clear p0 p1 p2 p3 p4 p5
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · clear p0 p1 p2 p3 p4 p5
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · clear p0 p1 p2 p3 p4 p5
    omega

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
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · clear p0 p1 p2 p3 p4 p5
    omega

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
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · clear p0 p1 p2 p3 p4 p5
    omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · clear p0 p1 p2 p3 p4 p5
    omega

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
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · clear p0 p1 p2 p3 p4 p5
    omega

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


end Collatz.Exploration.ElevenHalvesArithmetic
