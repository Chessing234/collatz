import Collatz.Strategy.ExcursionMap

/-!
# The two-step light block `(v, W) = (2, 1)`

Residue enumeration of never-drop candidates is dominated by consecutive
*light* excursions with `(v, W) = (2, 1)`: odd starts `n ≡ 11 (mod 16)` whose
landing stays in `3 (mod 4)`.  This file does not add another modulus.  It
names the exact two-step map on that dynamical class and records what the map
does *not* force.

## One step

From `IsExcursion n 2 u 1 e` one has `n = 4u − 1` with `u` odd and

  `e = (9u − 1) / 2`,

or, eliminating `u`,

  `e = (9n + 5) / 8`.

Each identity is an equality of naturals (`Nat.div`), not an approximation.

## Two steps

If the landing is itself a `(2, 1)` excursion, the composition is the affine
map with rational coefficients `81/64` and `85/64`:

  `e₂ = (81 n + 85) / 64`     (`= (81 u + 1) / 16`).

This holds for every `n` that actually takes two consecutive `(2, 1)` steps.
The two-step image is always strictly larger than the start (`2^{v+W} = 8 ≤ 9
= 3^v` at each factor), so two light steps never drop.

## Forced `v = 1`?

A `v = 1` landing would drop by `drop_of_v_one`.  Two consecutive `(2, 1)`
steps do **not** force that residue: the second landing of `251` is `319 ≡ 3
(mod 4)`.  The next excursion of that witness is again above the start
(`319 ↦ 911`).  There is therefore no theorem “every two-step light block
drops”, and none is claimed.
-/

namespace Collatz
namespace ExcursionBlock

open Collatz.Arith Collatz.ExcursionMap


/-! ## 1.  Unpacking a single `(2, 1)` excursion -/

/-- The defining equations at `(v, W) = (2, 1)`. -/
theorem eqs_of_v_two_W_one {n u e : Nat} (h : IsExcursion n 2 u 1 e) :
    n + 1 = 4 * u ∧ 9 * u = 2 * e + 1 := by
  have hnu := h.2.2.2.2.2.1
  have hpeak := h.2.2.2.2.2.2
  rw [show (2 : Nat) ^ 2 = 4 by decide] at hnu
  rw [show (3 : Nat) ^ 2 = 9 by decide, Nat.pow_one] at hpeak
  exact ⟨hnu, hpeak⟩

/-- **Start in cofactor coordinates.**  `v = 2` is `n = 4u − 1` with `u` odd. -/
theorem n_eq_of_v_two_W_one {n u e : Nat} (h : IsExcursion n 2 u 1 e) :
    n = 4 * u - 1 := by
  have ⟨hnu, _⟩ := eqs_of_v_two_W_one h
  omega

/-- The cofactor is odd, as required by `IsExcursion`. -/
theorem u_odd_of_v_two_W_one {n u e : Nat} (h : IsExcursion n 2 u 1 e) :
    u % 2 = 1 :=
  h.2.1


/-! ## 2.  Exact one-step landing -/

/-- **The one-step light map in the cofactor.**  For `n = 4u − 1` with
`(v, W) = (2, 1)`, the landing is `(9u − 1) / 2`. -/
theorem landing_u_of_v_two_W_one {n u e : Nat} (h : IsExcursion n 2 u 1 e) :
    e = (9 * u - 1) / 2 := by
  have ⟨_, hpeak⟩ := eqs_of_v_two_W_one h
  have hsub : 9 * u - 1 = 2 * e := by omega
  rw [hsub]
  exact (Nat.mul_div_cancel_left e (by omega : 0 < 2)).symm

/-- **The one-step light map in `n`.**  Same landing, affine form
`(9/8) n + 5/8`. -/
theorem landing_n_of_v_two_W_one {n u e : Nat} (h : IsExcursion n 2 u 1 e) :
    e = (9 * n + 5) / 8 := by
  have ⟨hnu, hpeak⟩ := eqs_of_v_two_W_one h
  have h8 : 8 * e = 9 * n + 5 := by omega
  have : 9 * n + 5 = 8 * e := h8.symm
  rw [this]
  exact (Nat.mul_div_cancel_left e (by omega : 0 < 8)).symm

/-- A single `(2, 1)` step is strictly expanding. -/
theorem v_two_W_one_grows {n u e : Nat} (h : IsExcursion n 2 u 1 e) : n < e := by
  have ⟨hnu, hpeak⟩ := eqs_of_v_two_W_one h
  omega


/-! ## 3.  Two consecutive `(2, 1)` steps: the affine block -/

/-- Intermediate cofactor of the second excursion. -/
theorem mid_cofactor_of_two_light {n u e u2 e2 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2) :
    8 * u2 = 9 * u + 1 := by
  have ⟨_, hp1⟩ := eqs_of_v_two_W_one h1
  have ⟨he, _⟩ := eqs_of_v_two_W_one h2
  omega

/-- **Two-step block in the cofactor.**  After two consecutive `(2, 1)`
excursions the state is `(81u + 1) / 16`. -/
theorem two_light_u {n u e u2 e2 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2) :
    e2 = (81 * u + 1) / 16 := by
  have ⟨_, hp1⟩ := eqs_of_v_two_W_one h1
  have ⟨he, hp2⟩ := eqs_of_v_two_W_one h2
  have h16 : 16 * e2 = 81 * u + 1 := by omega
  have : 81 * u + 1 = 16 * e2 := h16.symm
  rw [this]
  exact (Nat.mul_div_cancel_left e2 (by omega : 0 < 16)).symm

/-- **Two-step block in `n`.**  The exact integer identity

  `e₂ = (81 n + 85) / 64`

for every start that takes two consecutive `(2, 1)` excursions.  Rational
form: `n ↦ (81/64) n + 85/64`. -/
theorem two_light_n {n u e u2 e2 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2) :
    e2 = (81 * n + 85) / 64 := by
  have ⟨hn, hp1⟩ := eqs_of_v_two_W_one h1
  have ⟨he, hp2⟩ := eqs_of_v_two_W_one h2
  have h64 : 64 * e2 = 81 * n + 85 := by omega
  have : 81 * n + 85 = 64 * e2 := h64.symm
  rw [this]
  exact (Nat.mul_div_cancel_left e2 (by omega : 0 < 64)).symm

/-- Two consecutive light steps never drop: the block is expanding. -/
theorem two_light_grows {n u e u2 e2 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2) :
    n < e2 := by
  have ⟨hn, hp1⟩ := eqs_of_v_two_W_one h1
  have ⟨he, hp2⟩ := eqs_of_v_two_W_one h2
  omega


/-! ## 4.  `v = 1` is not forced; two light steps do not force a drop -/

/-- Contrast: some two-step light blocks *do* land on `v = 1`
(`157 ≡ 1 (mod 4)`).  This is not used as a covering law. -/
theorem one_two_three_hits_v_one :
    IsExcursion 123 2 31 1 139 ∧
    IsExcursion 139 2 35 1 157 ∧
    157 % 4 = 1 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    rfl⟩

/-- **Witness that two consecutive `(2, 1)` steps do not force `v = 1`.**
`251 → 283 → 319` with `319 ≡ 3 (mod 4)`, so `drop_of_v_one` does not apply
to the second landing. -/
theorem two_light_not_force_v_one :
    IsExcursion 251 2 63 1 283 ∧
    IsExcursion 283 2 71 1 319 ∧
    319 % 4 = 3 ∧
    251 < 319 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    rfl, by omega⟩

/-- The same witness survives a third excursion: `319` has `(v, W) = (6, 2)`
and lands at `911 > 251`.  Two light steps do not force a later drop either. -/
theorem two_light_not_force_later_drop :
    IsExcursion 251 2 63 1 283 ∧
    IsExcursion 283 2 71 1 319 ∧
    IsExcursion 319 6 5 2 911 ∧
    251 < 911 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- Sanity check of the affine identity on the witness. -/
theorem two_light_n_on_witness :
    (81 * 251 + 85) / 64 = 319 := by
  decide

end ExcursionBlock
end Collatz

section AxiomAudit
open Collatz.ExcursionBlock
#print axioms landing_u_of_v_two_W_one
#print axioms landing_n_of_v_two_W_one
#print axioms two_light_u
#print axioms two_light_n
#print axioms two_light_grows
#print axioms two_light_not_force_v_one
#print axioms two_light_not_force_later_drop
end AxiomAudit
