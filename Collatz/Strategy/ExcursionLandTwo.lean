import Collatz.Strategy.ExcursionBlock
import Collatz.Strategy.ExcursionClock
import Collatz.Strategy.ExcursionPlusFive

/-!
# Two consecutive `(2, 1)` steps, then remainder `3`

A single `(v, W) = (2, 1)` light step grows by `9/8` (`eight_clock`:
`8(e + 5) = 9(n + 5)`).  If that landing has `v₂(e + 5) = 3`, then
`e ≡ 3 (mod 16)` and `drop_of_three_mod_sixteen` fires on `e`.  The
one-step case is the class `59 (mod 128)` (`r = v₂(n + 5) = 6`), already
closed; this file does not redo that modulus.

Here the start takes **two** consecutive `(2, 1)` steps
(`ExcursionBlock.two_light_n`: `e₂ = (81 n + 85) / 64`), and the second
landing has remainder `3`.  The fuel identity spends three 2-factors per
light step, so `v₂(n + 5) = 9` and `v₂(e₂ + 5) = 3`.  The third
excursion is a `v = 2`, `W ≥ 2` drop.  Growth

  `(9/8)² · (9/16) = 729/1024 < 1`

puts the `W = 2` upper bound already below the original start, hence
every larger `W` as well.  The bound is attained (`1531 → 1723 → 1939 →
1091`).
-/

namespace Collatz
namespace ExcursionLandTwo

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionBlock Collatz.ExcursionClock Collatz.ExcursionExit
open Collatz.ExcursionPlusFive


/-! ## 1.  Fuel after two lights, and the exit residue -/

/-- Two consecutive `(2, 1)` steps with remainder `3` at the second
landing force `v₂(n + 5) = 9`. -/
theorem two_light_then_three_fuel {n u e u2 e2 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (hrem : Val2 (e2 + 5) 3) : Val2 (n + 5) 9 := by
  have hmid : Val2 (e + 5) 6 := by
    have := val2_plus_five_shift h2 hrem
    simpa using this
  have := val2_plus_five_shift h1 hmid
  simpa using this

/-- Remainder `3` at the second landing is `e₂ ≡ 3 (mod 16)`. -/
theorem e2_three_mod_sixteen {n u e u2 e2 : Nat}
    (_h1 : IsExcursion n 2 u 1 e) (_h2 : IsExcursion e 2 u2 1 e2)
    (hrem : Val2 (e2 + 5) 3) : e2 % 16 = 3 := by
  have hpow : (2 : Nat) ^ (3 + 1) = 16 := by decide
  have : (e2 + 5) % 16 = 8 := by
    have := Val2.mod hrem
    rwa [hpow] at this
  omega


/-! ## 2.  The `W = 2` upper bound, and the two-step clock -/

private theorem four_le_two_pow {W : Nat} (hW : 2 ≤ W) : 4 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 2 ≤ 2 ^ W := two_pow_le_two_pow hW
  simpa using this

/-- **`W = 2` upper bound.**  A `v = 2`, `W ≥ 2` landing satisfies
`16 e ≤ 9 m + 5`, with equality at `W = 2`. -/
theorem landing_upper_of_v_two_W_ge_two {m um Wm em : Nat}
    (h : IsExcursion m 2 um Wm em) (hW : 2 ≤ Wm) :
    16 * em ≤ 9 * m + 5 := by
  have hnu : m + 1 = 4 * um := by
    have := h.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak : 9 * um = 2 ^ Wm * em + 1 := by
    have := h.2.2.2.2.2.2
    rw [show (3 : Nat) ^ 2 = 9 by decide] at this
    exact this
  have h4 := four_le_two_pow hW
  have hle : 4 * em ≤ 9 * um - 1 := by
    have hmul : 4 * em ≤ 2 ^ Wm * em := Nat.mul_le_mul_right em h4
    have : 2 ^ Wm * em = 9 * um - 1 := by omega
    omega
  have hscale : 4 * (9 * um - 1) = 9 * m + 5 := by omega
  have hmul : 4 * (4 * em) ≤ 4 * (9 * um - 1) := Nat.mul_le_mul_left 4 hle
  have h16 : (16 : Nat) * em = 4 * (4 * em) := by omega
  omega

/-- Integer form of `two_light_n`. -/
theorem two_light_clock {n u e u2 e2 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2) :
    64 * e2 = 81 * n + 85 := by
  have ⟨hnu, hp1⟩ := eqs_of_v_two_W_one h1
  have ⟨he, hp2⟩ := eqs_of_v_two_W_one h2
  omega

/-- Compose the two-step clock with the `W = 2` bound:
`1024 e₃ ≤ 729 n + 1085`. -/
theorem compose_W_two_bound {n e2 e3 : Nat}
    (h64 : 64 * e2 = 81 * n + 85) (h16 : 16 * e3 ≤ 9 * e2 + 5) :
    1024 * e3 ≤ 729 * n + 1085 := by
  have hL : 64 * (16 * e3) = 1024 * e3 := by
    have hconst : (64 : Nat) * 16 = 1024 := by decide
    rw [← Nat.mul_assoc, hconst]
  have hmul : 64 * (16 * e3) ≤ 64 * (9 * e2 + 5) := Nat.mul_le_mul_left 64 h16
  have hr : 64 * (9 * e2 + 5) = 9 * (64 * e2) + 320 := by
    have hadd : 64 * (9 * e2 + 5) = 64 * (9 * e2) + 64 * 5 := Nat.mul_add _ _ _
    have h5 : (64 : Nat) * 5 = 320 := by decide
    have h9 : 64 * (9 * e2) = 9 * (64 * e2) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hadd, h5, h9]
  have hr2 : 9 * (64 * e2) + 320 = 9 * (81 * n + 85) + 320 := by rw [h64]
  have hr3 : 9 * (81 * n + 85) + 320 = 729 * n + 1085 := by
    have hdist : 9 * (81 * n + 85) = 9 * (81 * n) + 9 * 85 := Nat.mul_add 9 (81 * n) 85
    have h729 : 9 * (81 * n) = 729 * n := by
      have hc : (9 : Nat) * 81 = 729 := by decide
      rw [← Nat.mul_assoc, hc]
    have h765 : (9 : Nat) * 85 = 765 := by decide
    have hsum : (765 : Nat) + 320 = 1085 := by decide
    rw [hdist, h729, h765, Nat.add_assoc, hsum]
  calc
    1024 * e3 = 64 * (16 * e3) := hL.symm
    _ ≤ 64 * (9 * e2 + 5) := hmul
    _ = 9 * (64 * e2) + 320 := hr
    _ = 9 * (81 * n + 85) + 320 := hr2
    _ = 729 * n + 1085 := hr3

/-- The composition is strictly contracting once `n ≥ 11`
(every `(2, 1)` start). -/
private theorem drop_coeff {n : Nat} (h : 11 ≤ n) :
    729 * n + 1085 < 1024 * n := by
  have h295 : 1085 < 295 * n := by
    have hmin : 295 * 11 ≤ 295 * n := Nat.mul_le_mul_left 295 h
    have hnum : (1085 : Nat) < 295 * 11 := by decide
    omega
  have hsum : (729 : Nat) + 295 = 1024 := by decide
  have hsplit : 729 * n + 295 * n = 1024 * n := by
    rw [← Nat.add_mul, hsum]
  omega


/-! ## 3.  The third landing sits below the original start -/

/-- **Two consecutive `(2, 1)` steps with remainder `3` at the second
landing drop below the original start.**  The third excursion is a
`v = 2`, `W ≥ 2` drop; the `W = 2` upper bound is already `(729 n + 1085)
/ 1024 < n`. -/
theorem lemmaX_of_two_light_then_three {n u e u2 e2 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (hrem : Val2 (e2 + 5) 3) (hn : 1 < n) :
    ∃ e3 : Nat, ExChain n e3 ∧ e3 < n := by
  have he16 := e2_three_mod_sixteen h1 h2 hrem
  have he2odd : e2 % 2 = 1 := h2.2.2.1
  obtain ⟨v3, u3, W3, e3, hex3⟩ := exists_excursion he2odd
  have ⟨hv3, hW3⟩ := (v_two_W_ge_two_iff hex3).mpr he16
  have hv3' : v3 = 2 := hv3
  subst hv3'
  have h16 := landing_upper_of_v_two_W_ge_two hex3 hW3
  have h64 := two_light_clock h1 h2
  have h1024 := compose_W_two_bound h64 h16
  have hn11 : 11 ≤ n := by
    have hmod : n % 16 = 11 := (v_two_W_one_iff h1).mp ⟨rfl, rfl⟩
    omega
  have hcoeff := drop_coeff hn11
  have hdrop : e3 < n := by
    have : 1024 * e3 < 1024 * n := Nat.lt_of_le_of_lt h1024 hcoeff
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨e3, ?_, hdrop⟩
  exact ExChain.cons ⟨2, u, 1, h1⟩
    (ExChain.cons ⟨2, u2, 1, h2⟩ (ExChain.one ⟨2, u3, W3, hex3⟩))


/-! ## 4.  Witness: the `W = 2` bound is attained and still drops -/

/-- `1531` takes two `(2, 1)` steps, lands with `v₂(e₂ + 5) = 3`, and
the third excursion has `W = 2` at `1091 < 1531`.  Fuel: `v₂(1531 + 5) = 9`. -/
theorem fifteen_thirty_one_two_light_then_three :
    IsExcursion 1531 2 383 1 1723 ∧
    IsExcursion 1723 2 431 1 1939 ∧
    Val2 (1939 + 5) 3 ∧
    IsExcursion 1939 2 485 2 1091 ∧
    1091 < 1531 ∧
    Val2 (1531 + 5) 9 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨243, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega,
    ⟨3, rfl, rfl⟩⟩

end ExcursionLandTwo
end Collatz

section AxiomAudit
open Collatz.ExcursionLandTwo
#print axioms two_light_then_three_fuel
#print axioms e2_three_mod_sixteen
#print axioms landing_upper_of_v_two_W_ge_two
#print axioms two_light_clock
#print axioms compose_W_two_bound
#print axioms lemmaX_of_two_light_then_three
end AxiomAudit
