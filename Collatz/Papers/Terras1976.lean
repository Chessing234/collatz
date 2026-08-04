import Collatz.Basic
import Collatz.Accelerated

/-! Lean notes for Riho Terras,
"A stopping time problem on the positive integers",
Acta Arithmetica 30 (1976), 241--252.

Terras introduced the accelerated 3x+1 map `T(n) = (3n+1)/2` for odd `n`
and `T(n) = n/2` for even `n` (the same accelerated map recorded in
`Collatz.Accelerated` and in `Collatz.Papers.Lagarias2003Bibliography`) and
defined the *stopping time* `σ(n)` as the least `k ≥ 1` with `T^k(n) < n`.
His celebrated result is that the set of positive integers with a finite
stopping time has natural density `1`.

The density theorem is recorded below as a proposition, not as a theorem.
The shared accelerated-orbit definitions in `Collatz.Accelerated` provide the
stopping-time predicate, checked finite stopping-time instances, and the
affine parity-vector identity.  This file keeps the bibliographic wrapper
and a few Terras-specific statements.

Source: Acta Arith. 30 (1976), 241--252; see also the MathWorld entry
"Collatz Problem" and Lagarias's annotated bibliography (arXiv:math/0309224).
A finer density-existence result appears in Terras, "On the existence of a
density", Acta Arith. 35 (1979), 101--102.
-/

namespace Collatz.Papers.Terras1976

/-- Re-export the citation-friendly name for the accelerated step. -/
abbrev acceleratedStep : Nat → Nat := Collatz.acceleratedStep

/-- Re-export the citation-friendly name for the accelerated orbit. -/
abbrev acceleratedOrbit : Nat → Nat → Nat := Collatz.acceleratedOrbit

/-- Re-export Terras's stopping-time predicate. -/
abbrev hasFiniteStoppingTime : Nat → Prop := Collatz.hasFiniteStoppingTime

/-- Terras (1976), main result (recorded, not proved): the set of positive
    integers with a finite stopping time has natural density `1`.  The count
    uses the bounded approximation `hasStoppingTimeBy n N`. -/
def terrasDensityOne : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (Collatz.countUpTo (fun n => Collatz.hasStoppingTimeBy n N = true) N : Rat)

/-- The input `2` has a finite stopping time. -/
theorem hasFiniteStoppingTime_two : hasFiniteStoppingTime 2 :=
  Collatz.hasFiniteStoppingTime_of_even (by omega) (by decide)

/-- The input `3` has a finite stopping time (`σ(3) = 4`). -/
theorem hasFiniteStoppingTime_three : hasFiniteStoppingTime 3 := by
  exact ⟨4, ⟨by omega, by decide⟩⟩

/-- The input `4` has a finite stopping time. -/
theorem hasFiniteStoppingTime_four : hasFiniteStoppingTime 4 :=
  Collatz.hasFiniteStoppingTime_of_even (by omega) (by decide)

/-- The input `5` has a finite stopping time (`σ(5) = 2`). -/
theorem hasFiniteStoppingTime_five : hasFiniteStoppingTime 5 := by
  exact ⟨2, ⟨by omega, by decide⟩⟩

/-- The input `6` has a finite stopping time. -/
theorem hasFiniteStoppingTime_six : hasFiniteStoppingTime 6 :=
  Collatz.hasFiniteStoppingTime_of_even (by omega) (by decide)

/-- The input `7` has a finite stopping time (`σ(7) = 7`). -/
theorem hasFiniteStoppingTime_seven : hasFiniteStoppingTime 7 := by
  exact ⟨7, ⟨by omega, by decide⟩⟩

/-- The input `8` has a finite stopping time. -/
theorem hasFiniteStoppingTime_eight : hasFiniteStoppingTime 8 :=
  Collatz.hasFiniteStoppingTime_of_even (by omega) (by decide)

/-- The input `16` has a finite stopping time. -/
theorem hasFiniteStoppingTime_sixteen : hasFiniteStoppingTime 16 :=
  Collatz.hasFiniteStoppingTime_of_even (by omega) (by decide)

/-- Doubling preserves finite stopping time: if `m` has finite stopping time,
so does `2m` (the orbit halves on the first accelerated step). -/
theorem hasFiniteStoppingTime_double {m : Nat} (hm : hasFiniteStoppingTime m) :
    hasFiniteStoppingTime (2 * m) :=
  Collatz.hasFiniteStoppingTime_of_double hm

/-- Multiplying by a positive power of two preserves finite stopping time. -/
theorem hasFiniteStoppingTime_multiple {m a : Nat} (hm : hasFiniteStoppingTime m) (ha : 0 < a) :
    hasFiniteStoppingTime (2^a * m) :=
  Collatz.hasFiniteStoppingTime_of_multiple hm ha

/-- The parity vector of length `k` is periodic with period `2^k`. This is a
key structural lemma toward Terras's density-`1` stopping-time theorem. -/
theorem parityVector_periodic (n k : Nat) :
    Collatz.parityVector n k = Collatz.parityVector (n % 2^k) k :=
  Collatz.parityVector_mod_pow_two n k

/-- Distinct residues below `2^k` give distinct parity vectors of length `k`. -/
theorem parityVector_injective (a b k : Nat) (ha : a < 2^k) (hb : b < 2^k) :
    Collatz.parityVector a k = Collatz.parityVector b k → a = b :=
  Collatz.parityVector_injective_mod_pow_two k a b ha hb

/-- Every binary pattern of length `k` occurs as a parity vector. In other
words, the map `a ↦ parityVector a k` from `Fin (2^k)` to `{0,1}^k` is
surjective (and hence bijective). -/
theorem parityVector_surjective (k : Nat) (p : List Nat)
    (hp : p.length = k) (hpval : ∀ x ∈ p, x = 0 ∨ x = 1) :
    ∃ a : Nat, a < 2^k ∧ Collatz.parityVector a k = p :=
  Collatz.parityVector_surjective_mod_pow_two k p hp hpval

/-- The input `9` has a finite stopping time (`σ(9) = 2`). -/
theorem hasFiniteStoppingTime_nine : hasFiniteStoppingTime 9 := by
  exact ⟨2, ⟨by omega, by decide⟩⟩

/-- The input `10` has a finite stopping time. -/
theorem hasFiniteStoppingTime_ten : hasFiniteStoppingTime 10 :=
  Collatz.hasFiniteStoppingTime_of_even (by omega) (by decide)

/-- The input `12` has a finite stopping time. -/
theorem hasFiniteStoppingTime_twelve : hasFiniteStoppingTime 12 :=
  Collatz.hasFiniteStoppingTime_of_even (by omega) (by decide)

/-- The input `15` has a finite stopping time (`σ(15) = 7`). -/
theorem hasFiniteStoppingTime_fifteen : hasFiniteStoppingTime 15 := by
  exact ⟨7, ⟨by omega, by decide⟩⟩

/-- The input `18` has a finite stopping time. -/
theorem hasFiniteStoppingTime_eighteen : hasFiniteStoppingTime 18 :=
  Collatz.hasFiniteStoppingTime_of_even (by omega) (by decide)

/-- The input `20` has a finite stopping time. -/
theorem hasFiniteStoppingTime_twenty : hasFiniteStoppingTime 20 :=
  Collatz.hasFiniteStoppingTime_of_even (by omega) (by decide)

/-- The input `24` has a finite stopping time. -/
theorem hasFiniteStoppingTime_twentyfour : hasFiniteStoppingTime 24 :=
  Collatz.hasFiniteStoppingTime_of_even (by omega) (by decide)

/-- The input `32` has a finite stopping time. -/
theorem hasFiniteStoppingTime_thirtytwo : hasFiniteStoppingTime 32 :=
  Collatz.hasFiniteStoppingTime_of_even (by omega) (by decide)

end Collatz.Papers.Terras1976
