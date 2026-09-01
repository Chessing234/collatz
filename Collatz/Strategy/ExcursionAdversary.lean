import Collatz.Strategy.ExcursionMap
import Collatz.Strategy.ScaleRecord
import Collatz.Strategy.Denominator

/-!
# Adversary for one-excursion drop, and the next-odd formula

`drop_of_v_one` and `drop_of_v_two` (`W ≥ 2`) are proved in `ExcursionMap`.
This file checks that neither is an overclaim, and records the first-excursion
census plus the computational landing formula.

1. **`expStep` cannot satisfy `W ≥ 1`.**  After a maximal odd run the peak is
   even.  Collatz halves; `expStep` does `3x/2`.  A drop needs
   `3^v < 2^{v+W}` (`drop_needs_surplus`); with no extra halvings this is
   `3^v < 2^v`, which is false.  `expOrbit` never drops.

2. **`3x + d` can have `W ≥ 1` and still cycle.**  A one-step drop on a residue
   class of `3x + 1` does not claim a fact that would also kill the genuine
   cycles of `3x + 5` and `3x + 7`.  Those maps share the even contraction:
   `5 → 10 → 5` (`d = 5`, `W = 1`) and `5 → 11 → 20 → 10 → 5` (`d = 7`,
   `v = 2`, `W = 2`).

3. **Landing uniqueness, computationally.**  From `IsExcursion`,
   `e = (3^v * u - 1) / 2^W` as `Nat.div`.
-/

namespace Collatz
namespace ExcursionAdversary

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ScaleRecord Collatz.Denominator


/-! ## 1.  Next-odd formula -/

/-- **The landing is the odd cofactor of the peak, as `Nat.div`.**  Together
with uniqueness of `(v, u, W)` this is a function of the start. -/
theorem landing_div {n v u W e : Nat} (h : IsExcursion n v u W e) :
    e = (3 ^ v * u - 1) / 2 ^ W := by
  have hsub : 3 ^ v * u - 1 = 2 ^ W * e := by
    rw [h.2.2.2.2.2.2, Nat.add_sub_cancel]
  rw [hsub]
  exact (Nat.mul_div_cancel_left e (two_pow_pos W)).symm


/-! ## 2.  `expStep` cannot satisfy `W ≥ 1` -/

/-- The even branch of `expStep` is `3x/2`, not `x/2`. -/
theorem expStep_even_branch {x : Nat} (he : x % 2 = 0) :
    expStep x = 3 * x / 2 := by
  unfold expStep
  rw [if_pos he]

/-- Collatz's even contraction is not a step of `expStep`. -/
theorem expStep_even_ne_half {x : Nat} (he : x % 2 = 0) (hx : 1 < x) :
    expStep x ≠ x / 2 := by
  rw [expStep_even_branch he]
  omega

/-- After a genuine excursion the peak is even, and `expStep` triples-and-halves
it rather than dividing by `2^W`. -/
theorem expStep_on_peak {n v u W e : Nat} (h : IsExcursion n v u W e) :
    expStep (3 ^ v * u - 1) = 3 * (3 ^ v * u - 1) / 2 := by
  have hval := val2_peak_of h
  have heven : (3 ^ v * u - 1) % 2 = 0 :=
    Val2.even_of_pos hval (IsExcursion.one_le_W h)
  exact expStep_even_branch heven

/-- The peak is positive, so `expStep` strictly grows there. -/
theorem expStep_grows_on_peak {n v u W e : Nat} (h : IsExcursion n v u W e) :
    3 ^ v * u - 1 < expStep (3 ^ v * u - 1) := by
  have hsub : 3 ^ v * u - 1 = 2 ^ W * e := by
    rw [h.2.2.2.2.2.2, Nat.add_sub_cancel]
  have hepos : 0 < e := by
    have : e % 2 = 1 := h.2.2.1
    omega
  have hpos : 0 < 3 ^ v * u - 1 := by
    rw [hsub]
    exact Nat.mul_pos (two_pow_pos W) hepos
  exact expStep_gt hpos

/-- Extra halvings are what a drop consumes: `W = 0` cannot beat `log₂ 3`. -/
theorem three_pow_not_lt_two_pow (k : Nat) : ¬ (3 ^ k < 2 ^ k) := by
  have := two_pow_le_three_pow k
  omega

/-- The surplus test with no extra halvings is unsatisfiable.  This is the
`W`-slot that `expStep`'s even branch `3x/2` leaves empty. -/
theorem drop_impossible_without_W (v : Nat) : ¬ (3 ^ v < 2 ^ (v + 0)) := by
  rw [Nat.add_zero]
  exact three_pow_not_lt_two_pow v

/-- `expOrbit` never drops.  A one-excursion drop criterion that held of
`expStep` would be the wrong object. -/
theorem expOrbit_never_drops {x : Nat} (hx : 0 < x) (k : Nat) :
    x ≤ expOrbit k x := by
  have := expOrbit_ge k x hx
  omega


/-! ## 3.  `3x + d` can have `W ≥ 1` and still cycle -/

/-- **`d = 5`, `W = 1`, genuine cycle.**  One odd step, one even contraction,
return.  The even branch is used, and there is no drop. -/
theorem three_x_plus_five_W_one_cycle :
    genStep 5 5 = 10 ∧ 10 % 2 = 0 ∧ genStep 5 10 = 5 ∧
      genOrbit 5 2 5 = 5 ∧ ¬ (5 < 5) := by
  decide

/-- The same cycle never drops. -/
theorem three_x_plus_five_five_never_drops : GenNeverDrops 5 5 :=
  five_genNeverDrops

/-- **`d = 5`, `W = 2` on the `19`-cycle.**  Three odd steps then two halvings,
and the landing is the start. -/
theorem three_x_plus_five_nineteen_W_two_cycle :
    genStep 5 19 = 31 ∧ genStep 5 31 = 49 ∧ genStep 5 49 = 76 ∧
      76 % 2 = 0 ∧ genStep 5 76 = 38 ∧ genStep 5 38 = 19 ∧
      genOrbit 5 5 19 = 19 := by
  decide

/-- **`d = 7`, `v = 2`, `W = 2`, genuine cycle.**  The `3x + 1` companion
(`v = 2` and `W ≥ 2` drops) is therefore not `d`-uniform: the same shape is a
cycle of `3x + 7`. -/
theorem three_x_plus_seven_v_two_W_two_cycle :
    genStep 7 5 = 11 ∧ 11 % 2 = 1 ∧
      genStep 7 11 = 20 ∧ 20 % 2 = 0 ∧
      genStep 7 20 = 10 ∧ genStep 7 10 = 5 ∧
      genOrbit 7 4 5 = 5 := by
  decide

/-- A one-step residue-class drop for `3x + 1` does not claim too much:
`W ≥ 1` (even `v = 2` and `W = 2`) occurs on genuine `3x + d` cycles. -/
theorem W_ge_one_does_not_kill_cycles :
    (genOrbit 5 2 5 = 5 ∧ 10 % 2 = 0) ∧
      (genOrbit 7 4 5 = 5 ∧ 20 % 2 = 0) := by
  decide


/-! ## 4.  First-excursion census -/

theorem seven_ex : IsExcursion 7 3 1 1 13 := seven_first_excursion

theorem eleven_ex : IsExcursion 11 2 3 1 13 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem fifteen_ex : IsExcursion 15 4 1 4 5 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem nineteen_ex : IsExcursion 19 2 5 2 11 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem twentythree_ex : IsExcursion 23 3 3 4 5 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem twentyseven_ex : IsExcursion 27 2 7 1 31 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem thirtyone_ex : IsExcursion 31 5 1 1 121 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem fortyseven_ex : IsExcursion 47 4 3 1 121 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem sixtythree_ex : IsExcursion 63 6 1 3 91 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem eleven_no_first_drop {e : Nat} (h : IsExcursion 11 2 3 1 e) : 11 ≤ e :=
  no_drop_of_light h (by decide)

theorem twentyseven_no_first_drop {e : Nat} (h : IsExcursion 27 2 7 1 e) :
    27 ≤ e :=
  no_drop_of_light h (by decide)

theorem thirtyone_no_first_drop {e : Nat} (h : IsExcursion 31 5 1 1 e) :
    31 ≤ e :=
  no_drop_of_light h (by decide)

theorem fortyseven_no_first_drop {e : Nat} (h : IsExcursion 47 4 3 1 e) :
    47 ≤ e :=
  no_drop_of_light h (by decide)

theorem sixtythree_no_first_drop {e : Nat} (h : IsExcursion 63 6 1 3 e) :
    63 ≤ e :=
  no_drop_of_light h (by decide)

/-- First-excursion `(v, u, W, e)` and whether `e < n`.

`15` and `23` drop inside the surviving classes; `7`, `11`, `27`, `31`, `47`,
`63` do not.  Lemma X is not a first-excursion statement.  (`11 ≡ 11 (mod 32)`
drops on the *second* excursion, already proved; `27 ≡ 27 (mod 32)` does not
drop first and remains open.) -/
theorem first_excursion_census :
    IsExcursion 7 3 1 1 13 ∧ ¬ (13 < 7) ∧
      IsExcursion 11 2 3 1 13 ∧ ¬ (13 < 11) ∧
      IsExcursion 15 4 1 4 5 ∧ 5 < 15 ∧
      IsExcursion 19 2 5 2 11 ∧ 11 < 19 ∧
      IsExcursion 23 3 3 4 5 ∧ 5 < 23 ∧
      IsExcursion 27 2 7 1 31 ∧ ¬ (31 < 27) ∧
      IsExcursion 31 5 1 1 121 ∧ ¬ (121 < 31) ∧
      IsExcursion 47 4 3 1 121 ∧ ¬ (121 < 47) ∧
      IsExcursion 63 6 1 3 91 ∧ ¬ (91 < 63) :=
  ⟨seven_ex, by omega, eleven_ex, by omega, fifteen_ex, by omega,
    nineteen_ex, by omega, twentythree_ex, by omega, twentyseven_ex, by omega,
    thirtyone_ex, by omega, fortyseven_ex, by omega, sixtythree_ex, by omega⟩

/-- Landing uniqueness on the census, as `Nat.div`. -/
theorem landing_div_census :
    (3 ^ 3 * 1 - 1) / 2 ^ 1 = 13 ∧
      (3 ^ 2 * 3 - 1) / 2 ^ 1 = 13 ∧
      (3 ^ 4 * 1 - 1) / 2 ^ 4 = 5 ∧
      (3 ^ 2 * 5 - 1) / 2 ^ 2 = 11 ∧
      (3 ^ 3 * 3 - 1) / 2 ^ 4 = 5 ∧
      (3 ^ 2 * 7 - 1) / 2 ^ 1 = 31 ∧
      (3 ^ 5 * 1 - 1) / 2 ^ 1 = 121 ∧
      (3 ^ 4 * 3 - 1) / 2 ^ 1 = 121 ∧
      (3 ^ 6 * 1 - 1) / 2 ^ 3 = 91 := by
  decide

theorem seven_landing_div : 13 = (3 ^ 3 * 1 - 1) / 2 ^ 1 := landing_div seven_ex
theorem twentyseven_landing_div : 31 = (3 ^ 2 * 7 - 1) / 2 ^ 1 := landing_div twentyseven_ex
theorem thirtyone_landing_div : 121 = (3 ^ 5 * 1 - 1) / 2 ^ 1 := landing_div thirtyone_ex
theorem sixtythree_landing_div : 91 = (3 ^ 6 * 1 - 1) / 2 ^ 3 := landing_div sixtythree_ex

end ExcursionAdversary
end Collatz

section AxiomAudit
open Collatz.ExcursionAdversary
#print axioms landing_div
#print axioms expStep_on_peak
#print axioms drop_impossible_without_W
#print axioms W_ge_one_does_not_kill_cycles
#print axioms first_excursion_census
end AxiomAudit
