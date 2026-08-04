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

end Collatz.Papers.Terras1976
