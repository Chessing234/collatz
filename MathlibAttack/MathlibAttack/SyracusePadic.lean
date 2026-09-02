import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

/-!
# The 2-adic Syracuse map — a device that needs Mathlib

The root `Collatz` library cannot name `ℤ_[2]`.  This file hosts the Syracuse
(odd-to-odd) map on the odd 2-adic integers, using Mathlib's `PadicInt` as the
type and `PadicInt.unitCoeff` as the stripping of `2`-powers.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace MathlibAttack.SyracusePadic

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Odd 2-adic integers: the units of `ℤ_[2]`.  Equivalently, `‖x‖ = 1`,
equivalently `x.valuation = 0`. -/
abbrev OddPadicInt : Type := (PadicInt 2)ˣ

/-- The 2-adic Syracuse map: `S x = (3x+1) / 2^{v₂(3x+1)}`.

Mathlib's `PadicInt.unitCoeff` *is* this formula: it returns the unit `u` in the
unique writing `y = u * 2^{v₂(y)}`.  Defined on those `x` with `3x+1 ≠ 0`
(i.e. `x ≠ -1/3` in `ℤ_[2]`). -/
noncomputable def S {x : ℤ_[2]} (hx : (3 : ℤ_[2]) * x + 1 ≠ 0) : OddPadicInt :=
  PadicInt.unitCoeff hx

private lemma isUnit_three : IsUnit (3 : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  change ‖((3 : ℕ) : ℤ_[2])‖ = 1
  rw [PadicInt.norm_natCast_eq_one_iff]
  decide

private lemma norm_three_mul_of_isUnit {x : ℤ_[2]} (hx : IsUnit x) :
    ‖(3 : ℤ_[2]) * x‖ = 1 := by
  rw [norm_mul, PadicInt.isUnit_iff.mp isUnit_three, PadicInt.isUnit_iff.mp hx,
    one_mul]

/-- For odd `x`, the naive map `x ↦ 3x/2` lands in `ℚ_[2] \ ℤ_[2]`:
`v₂(3x/2) = -1`, so the 2-adic norm is `2`. -/
private lemma three_mul_div_two_norm {x : ℤ_[2]} (hx : IsUnit x) :
    ‖(((3 : ℤ_[2]) * x : ℤ_[2]) : ℚ_[2]) / (2 : ℚ_[2])‖ = 2 := by
  have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
    simpa using (Padic.norm_p (p := 2))
  rw [norm_div, PadicInt.padic_norm_e_of_padicInt, norm_three_mul_of_isUnit hx, h2]
  norm_num

/-- **The maps are not the same.**

On every odd `x` with `3x+1 ≠ 0`, Syracuse is a 2-adic unit (`‖S x‖ = 1`) while
`3x/2` has 2-adic norm `2`.  They disagree as functions `ℤ_[2] → ℚ_[2]`.

This comparison is invisible on `ℕ`: for odd `n`, `3n/2` is not an integer, so
the no-Mathlib branch cannot even state the inequality in a common type. -/
theorem S_ne_three_mul_div_two {x : ℤ_[2]} (hx : IsUnit x)
    (h31 : (3 : ℤ_[2]) * x + 1 ≠ 0) :
    ((S h31 : ℤ_[2]) : ℚ_[2]) ≠ (((3 : ℤ_[2]) * x : ℤ_[2]) : ℚ_[2]) / 2 := by
  intro h
  have hS : ‖((S h31 : ℤ_[2]) : ℚ_[2])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_units (S h31)
  have h3 := three_mul_div_two_norm hx
  rw [h, h3] at hS
  norm_num at hS

end MathlibAttack.SyracusePadic
