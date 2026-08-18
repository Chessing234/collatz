import Collatz.Strategy.RunInvariance

/-!
# Cycles with a single odd run

A cycle whose shape is "`j` odd steps up, then nothing but halvings back down"
is completely solvable, and the solution excludes it outright in the range that
matters.

If `m` is the least point, `T^j(m)` the top of the run, and the remaining
`L − j` steps are all halvings, then `T^j(m) = 2^(L−j) · m`, and the run identity
`2^j (T^j(m) + 1) = 3^j (m + 1)` turns into the exact equation

`3 ^ j · (m + 1) = 2 ^ L · m + 2 ^ j`     (`one_run_equation`)

equivalently `m · (2^L − 3^j) = 3^j − 2^j`.  Two consequences follow with no
computation at all:

* `3 ^ j < 2 ^ L` (`three_pow_lt_two_pow_of_one_run`);
* **`m + 2 ^ j ≤ 3 ^ j`** (`size_bound_of_one_run`) — the least point is bounded
  by the run length alone.

The second is the useful one, because it is an *upper* bound on `m`, and the
project has a *lower* bound: `m ≥ 307 200`.  So `3 ^ j > 307 200`, forcing
`j ≥ 12` (`twelve_le_run_of_one_run`).

This is the first place in the development where the verified range is used
**quantitatively** rather than as a threshold, and that matters: the mirror
analysis in `Mirror` shows every other tool here is blind to the `+1` in
`3n + 1`, so any completion must lean on the verified range in exactly this way.

Measured (not proved here): searching `j ≤ 4000` with the minimal `L` at each
`j`, there is no integer solution with `m ≥ 2` at all, and the largest value the
ratio `(3^j − 2^j)/(2^L − 3^j)` attains is `1243` — a factor of `247` below the
verified range.  The growth of that maximum is governed by the continued-fraction
denominators of `log₂ 3`, so `j` of order `10^5` is needed before it can even
reach `307 200`.  The unbounded tail is the usual linear-forms barrier; the
finite part is cheap and the margin enormous.
-/

namespace Collatz
namespace OneRunCycle

open Reach Congruence NeverDrops

/-! ## The exact equation -/

/-- **A one-odd-run cycle is an exact Diophantine equation.**  `j` odd steps up
followed by pure halving back to `m` forces `3 ^ j (m+1) = 2 ^ L m + 2 ^ j`. -/
theorem one_run_equation {m j L : Nat} (hjL : j ≤ L) (hrun : OddRuns.OddRun m j)
    (hdesc : acceleratedOrbit j m = 2 ^ (L - j) * m) :
    3 ^ j * (m + 1) = 2 ^ L * m + 2 ^ j := by
  have hval : 2 ^ j * (acceleratedOrbit j m + 1) = 3 ^ j * (m + 1) :=
    RunValue.oddRun_value j m hrun
  rw [hdesc] at hval
  have hsplit : (2:Nat) ^ j * (2 ^ (L - j) * m) = 2 ^ L * m := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  rw [Nat.mul_add, Nat.mul_one, hsplit] at hval
  omega

/-! ## Consequences -/

/-- The run cannot outgrow the cycle: `3 ^ j < 2 ^ L`. -/
theorem three_pow_lt_two_pow_of_one_run {m j L : Nat} (hj : 0 < j) (_hm : 0 < m)
    (heq : 3 ^ j * (m + 1) = 2 ^ L * m + 2 ^ j) : 3 ^ j < 2 ^ L := by
  rcases Nat.lt_or_ge (3 ^ j) (2 ^ L) with h | h
  · exact h
  · exfalso
    have hlt : (2:Nat) ^ j < 3 ^ j := RunValue.two_pow_lt_three_pow j hj
    have hmono : 2 ^ L * m ≤ 3 ^ j * m := Nat.mul_le_mul_right _ h
    have hexp : (3:Nat) ^ j * (m + 1) = 3 ^ j * m + 3 ^ j := by
      rw [Nat.mul_add, Nat.mul_one]
    omega

/-- **The least point is bounded by the run length**: `m + 2 ^ j ≤ 3 ^ j`. -/
theorem size_bound_of_one_run {m j L : Nat} (hj : 0 < j) (hm : 0 < m)
    (heq : 3 ^ j * (m + 1) = 2 ^ L * m + 2 ^ j) : m + 2 ^ j ≤ 3 ^ j := by
  have hlt := three_pow_lt_two_pow_of_one_run hj hm heq
  have hmono : (3 ^ j + 1) * m ≤ 2 ^ L * m := Nat.mul_le_mul_right _ (by omega)
  have hexp : ((3:Nat) ^ j + 1) * m = 3 ^ j * m + m := by
    rw [Nat.add_mul, Nat.one_mul]
  have hexp2 : (3:Nat) ^ j * (m + 1) = 3 ^ j * m + 3 ^ j := by
    rw [Nat.mul_add, Nat.mul_one]
  omega

/-- **A one-odd-run cycle needs a run of length at least twelve.**  The least
point of a counterexample is at least `307 200`, and `3 ^ 11 = 177 147` is too
small to bound it. -/
theorem twelve_le_run_of_one_run {m j L : Nat} (hj : 0 < j) (hge : 307200 ≤ m)
    (heq : 3 ^ j * (m + 1) = 2 ^ L * m + 2 ^ j) : 12 ≤ j := by
  have hsize := size_bound_of_one_run hj (by omega) heq
  rcases Nat.lt_or_ge j 12 with hlt | hge'
  · exfalso
    have hmono : (3:Nat) ^ j ≤ 3 ^ 11 := Arith.three_pow_le_three_pow (by omega)
    have h11 : (3:Nat) ^ 11 = 177147 := by decide
    rw [h11] at hmono
    generalize (3:Nat) ^ j = A at hsize hmono
    generalize (2:Nat) ^ j = B at hsize
    omega
  · exact hge'

/-- The chain, assembled: a one-odd-run cycle at a counterexample's least point
satisfies the exact equation, has `3 ^ j < 2 ^ L`, is bounded by
`m + 2 ^ j ≤ 3 ^ j`, and needs `j ≥ 12`. -/
theorem one_run_profile {m j L : Nat} (hj : 0 < j) (hjL : j ≤ L) (hge : 307200 ≤ m)
    (hrun : OddRuns.OddRun m j) (hdesc : acceleratedOrbit j m = 2 ^ (L - j) * m) :
    3 ^ j * (m + 1) = 2 ^ L * m + 2 ^ j ∧ 3 ^ j < 2 ^ L ∧
    m + 2 ^ j ≤ 3 ^ j ∧ 12 ≤ j := by
  have heq := one_run_equation hjL hrun hdesc
  exact ⟨heq, three_pow_lt_two_pow_of_one_run hj (by omega) heq,
    size_bound_of_one_run hj (by omega) heq, twelve_le_run_of_one_run hj hge heq⟩

end OneRunCycle
end Collatz
