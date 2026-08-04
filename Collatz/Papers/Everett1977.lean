import Collatz.Basic
import Collatz.Accelerated

/-! Lean notes for C. J. Everett,
"Iteration of the number-theoretic function f(2n)=n, f(2n+1)=3n+2",
Advances in Mathematics 25 (1977), 42--45.

Everett studied the accelerated `3x+1` iteration from a probabilistic point
of view.  His function `f` is exactly the accelerated map
`T(n) = n/2` (even) and `(3n+1)/2` (odd) on the positive integers.  He
showed that for almost all starting values (in a suitable sense related to
dyadic parity patterns) the iterates eventually fall below the starting value,
i.e. have a finite stopping time.

This file records Everett's density/stopping-time result as a proposition and
proves a few elementary parity-pattern facts that underlie his analysis.

Source: C. J. Everett, Iteration of the number-theoretic function
f(2n)=n, f(2n+1)=3n+2, Adv. Math. 25 (1977), 42--45.
-/

namespace Collatz.Papers.Everett1977

/-- Exact source tracked by this file. -/
def citation : String :=
  "C. J. Everett, Iteration of the number-theoretic function f(2n)=n, f(2n+1)=3n+2, Adv. Math. 25 (1977), 42--45."

/-- Everett's map `f` is the accelerated Collatz step. -/
theorem everett_map_eq_acceleratedStep (n : Nat) :
    (if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) = Collatz.acceleratedStep n := by
  simp [Collatz.acceleratedStep]

/-- The parity of the first iterate determines whether one or two standard
Collatz steps are folded into the accelerated step. -/
theorem parity_of_first_iterate (n : Nat) :
    Collatz.acceleratedStep n % 2 = (if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) % 2 := by
  simp [Collatz.acceleratedStep]

/-- For every length `j`, the parity vector of length `j` is a computable
function of the starting value. -/
theorem parity_vector_computable (n j : Nat) :
    Collatz.parityVector n j =
      (List.range j).map (fun i => (Collatz.acceleratedOrbit i n) % 2) := by
  simp [Collatz.parityVector]

/-- The parity vector of length `k` is periodic with period `2^k`.  This
congruence structure underlies Everett's probabilistic analysis of the
accelerated map. -/
theorem parity_vector_periodic (n k : Nat) :
    Collatz.parityVector n k = Collatz.parityVector (n % 2^k) k :=
  Collatz.parityVector_mod_pow_two n k

/-- Distinct residues below `2^k` give distinct parity vectors of length `k`. -/
theorem parity_vector_injective (a b k : Nat) (ha : a < 2^k) (hb : b < 2^k) :
    Collatz.parityVector a k = Collatz.parityVector b k → a = b :=
  Collatz.parityVector_injective_mod_pow_two k a b ha hb

/-- Every binary pattern of length `k` occurs as a parity vector.  In other
words, the map `a ↦ parityVector a k` from `Fin (2^k)` to `{0,1}^k` is a
bijection.  This equidistribution is the heart of Everett's density argument. -/
theorem parity_vector_surjective (k : Nat) (p : List Nat)
    (hp : p.length = k) (hpval : ∀ x ∈ p, x = 0 ∨ x = 1) :
    ∃ a : Nat, a < 2^k ∧ Collatz.parityVector a k = p :=
  Collatz.parityVector_surjective_mod_pow_two k p hp hpval

/-- Everett (1977), main result (recorded, not proved): the set of positive
integers with a finite stopping time under the accelerated map has natural
density `1`.  The count uses the bounded approximation
`hasStoppingTimeBy n N`. -/
def everettStoppingTimeDensityOne : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat)
        ≤ (Collatz.countUpTo (fun n => Collatz.hasStoppingTimeBy n N = true) N : Rat)

end Collatz.Papers.Everett1977
