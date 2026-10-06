import Collatz.Exploration.ThreePowerLift

/-!
# Covering the three lifts of a ternary unit

If q is a positive multiple of three and c = 1 modulo three, multiplication
by 1+q*c cycles through the three lifts of any unit residue modulo q.
The proof below constructs the required exponent t in {0,1,2}. It uses only
natural arithmetic and a kernel-checked three-element multiplication table.

This is a local arithmetic step for proving that powers of two cover units
modulo powers of three. It does not assume or imply Collatz convergence.
-/
namespace Collatz.Exploration.ThreeUnitLift

/-- Every nonzero ternary digit translates through all three digits. -/
theorem digit_cover (a b r : Fin 3) (hr : r.val ≠ 0) :
    ∃ t : Fin 3, (a.val+t.val*r.val)%3 = b.val := by
  have h : ∀ a b r : Fin 3, r.val ≠ 0 →
      ∃ t : Fin 3, (a.val+t.val*r.val)%3 = b.val := by decide
  exact h a b r hr

/-- Correction coefficients for the only three exponents needed by the lift. -/
def correction (y q c t : Nat) : Nat :=
  if t = 0 then 0 else if t = 1 then y*c else 2*y*c+q*y*c*c

/-- The square expansion is expressed without natural subtraction. -/
theorem square_one_add (x : Nat) : (1+x)^2 = 1+2*x+x*x := by
  simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
  omega

/-- Multiplication by the lifting factor has this exact correction. -/
theorem power_correction (y q c t : Nat) (ht : t ≤ 2) :
    y*(1+q*c)^t = y+q*correction y q c t := by
  have hcases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases hcases with h | h | h <;> subst t
  · simp [correction]
  · rw [Nat.pow_one]
    change y*(1+q*c) = y+q*(y*c)
    rw [Nat.mul_add, Nat.mul_one]
    congr 1
    ac_rfl
  · change y*(1+q*c)^2 = y+q*(2*y*c+q*y*c*c)
    rw [square_one_add, Nat.mul_add, Nat.mul_add, Nat.mul_one]
    have h1 : y*(2*(q*c)) = q*(2*y*c) := by ac_rfl
    have h2 : y*(q*c*(q*c)) = q*(q*y*c*c) := by ac_rfl
    rw [h1, h2, Nat.mul_add]
    omega

/-- The correction digit is the expected multiple of the input's unit digit. -/
theorem correction_mod_three (y q c t : Nat) (ht : t ≤ 2)
    (hq : q%3 = 0) (hc : c%3 = 1) :
    correction y q c t % 3 = (t*(y%3))%3 := by
  have hcases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases hcases with h | h | h <;> subst t <;>
    simp [correction, Nat.add_mod, Nat.mul_mod, hq, hc]

/-- Equal lower residues and equal quotient digits give equal lifted residues. -/
theorem lifted_congruence (y z q s : Nat) (hres : y%q = z%q)
    (hdigit : (y/q+s)%3 = (z/q)%3) :
    (y+q*s)%(q*3) = z%(q*3) := by
  have hy : y+q*s = y%q+q*(y/q+s) := by
    have h := Nat.mod_add_div y q
    rw [Nat.mul_add]
    omega
  have hz : z = z%q+q*(z/q) := (Nat.mod_add_div z q).symm
  calc
    (y+q*s)%(q*3) = (y%q+q*(y/q+s))%(q*3) := by rw [hy]
    _ = ((y%q)%(q*3)+q*((y/q+s)%3))%(q*3) := by
      rw [Nat.add_mod, Nat.mul_mod_mul_left]
    _ = ((z%q)%(q*3)+q*((z/q)%3))%(q*3) := by rw [hres, hdigit]
    _ = (z%q+q*(z/q))%(q*3) := by
      have hscale := Nat.mul_mod_mul_left q (z/q) 3
      have hsum := congrArg (fun v => ((z%q)%(q*3)+v)%(q*3)) hscale
      exact ((Nat.add_mod (z%q) (q*(z/q)) (q*3)).trans hsum).symm
    _ = z%(q*3) := by rw [← hz]

/-- The three possible powers cover every lifted unit residue. -/
theorem three_lifts (y z q c : Nat) (hy : y%3 ≠ 0)
    (hq : q%3 = 0) (hc : c%3 = 1) (hres : y%q = z%q) :
    ∃ t, t ≤ 2 ∧ (y*(1+q*c)^t)%(q*3) = z%(q*3) := by
  let a : Fin 3 := ⟨(y/q)%3, Nat.mod_lt _ (by decide)⟩
  let b : Fin 3 := ⟨(z/q)%3, Nat.mod_lt _ (by decide)⟩
  let r : Fin 3 := ⟨y%3, Nat.mod_lt _ (by decide)⟩
  obtain ⟨t, ht⟩ := digit_cover a b r hy
  have hbound : t.val ≤ 2 := by have := t.isLt; omega
  refine ⟨t.val, hbound, ?_⟩
  rw [power_correction y q c t.val hbound]
  apply lifted_congruence y z q _ hres
  rw [Nat.add_mod, correction_mod_three y q c t.val hbound hq hc]
  have hsolve : ((y/q)%3+t.val*(y%3))%3 = (z/q)%3 := ht
  simpa [Nat.add_mod] using hsolve

end Collatz.Exploration.ThreeUnitLift
