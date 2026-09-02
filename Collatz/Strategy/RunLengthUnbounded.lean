import Collatz.Strategy.MersenneDescent

/-!
# The tail cannot depend on the run length: a proof

`Strategy.RunLengthTail` exhibits five numbers with run length `r(n) = 2` and
stopping times up to `308`, which refutes any *specific* constant tail but leaves
open whether some finite `s(2)` works.  This file closes that.

The construction.  For `n ≡ 3 (mod 8)` — exactly the numbers with `r(n) = 2` —
writing `n = 8a + 3` gives

  `T(n) = 12a + 5`,  `T²(n) = 18a + 8`,  `T³(n) = 9a + 4`.

So choosing `a` with `9a + 5 = 2^k` lands the orbit exactly on `2^k − 1` after
three steps, and `ScaleLadder.climb` then carries it up to `3^k − 1` over the
next `k`.  Since `3^k − 1` dwarfs `n`, the orbit cannot have descended.

`9a + 5 = 2^k` is solvable precisely when `k ≡ 5 (mod 6)`, and the solutions obey
`a₀ = 3`, `a_{j+1} = 64a_j + 35`.  The first member is `n = 27`, whose long
trajectory is the standard example; the family continues
`1819, 116507, 7456539, …`.

**Conclusion.**  `no_tail_at_run_length_two`: for every bound `B` there is an `n`
with `n % 8 = 3` whose orbit is still above `n` after `B` steps.  So no `s` with
`T^(r(n) + s(r(n)))(n) < n` for all odd `n > 1` can exist — already at run
length `2`, the descent time is unbounded while the run length is pinned.

This answers the question in `PROGRAM_STATUS` in the negative for the refined
reading, and locates the obstruction: not in the `2^j − 1` family it proposed
(which `Strategy.MersenneDescent` shows descends within `12j`), but at small
fixed run length.
-/

namespace Collatz
namespace RunLengthUnbounded

open MersenneDescent

/-- `a₀ = 3`, `a_{j+1} = 64a_j + 35`: the solutions of `9a + 5 = 2^(6j+5)`. -/
def aSeq : Nat → Nat
  | 0 => 3
  | j + 1 => 64 * aSeq j + 35

theorem aSeq_spec : ∀ j : Nat, 9 * aSeq j + 5 = 2 ^ (6 * j + 5) := by
  intro j
  induction j with
  | zero => decide
  | succ j ih =>
    have hp : (2 : Nat) ^ (6 * (j + 1) + 5) = 64 * 2 ^ (6 * j + 5) := by
      have : 6 * (j + 1) + 5 = (6 * j + 5) + 6 := by omega
      rw [this, Nat.pow_add]
      omega
    show 9 * (64 * aSeq j + 35) + 5 = 2 ^ (6 * (j + 1) + 5)
    rw [hp]; omega

/-- The witness family, all `≡ 3 (mod 8)` and so all of run length exactly two. -/
def nSeq (j : Nat) : Nat := 8 * aSeq j + 3

theorem nSeq_mod_eight (j : Nat) : nSeq j % 8 = 3 := by
  show (8 * aSeq j + 3) % 8 = 3
  omega

/-- Three steps land the family exactly on `2^(6j+5) − 1`. -/
theorem nSeq_step_three (j : Nat) :
    acceleratedOrbit 3 (nSeq j) = 2 ^ (6 * j + 5) - 1 := by
  have hspec := aSeq_spec j
  have h1 : acceleratedStep (nSeq j) = 12 * aSeq j + 5 := by
    show acceleratedStep (8 * aSeq j + 3) = 12 * aSeq j + 5
    rw [acceleratedStep, if_neg (by omega)]
    omega
  have h2 : acceleratedStep (12 * aSeq j + 5) = 18 * aSeq j + 8 := by
    rw [acceleratedStep, if_neg (by omega)]
    omega
  have h3 : acceleratedStep (18 * aSeq j + 8) = 9 * aSeq j + 4 := by
    rw [acceleratedStep, if_pos (by omega)]
    omega
  show acceleratedOrbit 3 (nSeq j) = _
  rw [show (3 : Nat) = 2 + 1 from rfl, ← acceleratedOrbit_add,
      show acceleratedOrbit 1 (nSeq j) = acceleratedStep (nSeq j) from rfl, h1,
      show (2 : Nat) = 1 + 1 from rfl, ← acceleratedOrbit_add,
      show acceleratedOrbit 1 (12 * aSeq j + 5) = acceleratedStep (12 * aSeq j + 5) from rfl,
      h2, show acceleratedOrbit 1 (18 * aSeq j + 8) = acceleratedStep (18 * aSeq j + 8) from rfl,
      h3, ← hspec]
  omega

/-- …and `6j + 5` more carry it to the peak `3^(6j+5) − 1`. -/
theorem nSeq_peak (j : Nat) :
    acceleratedOrbit (6 * j + 5 + 3) (nSeq j) = 3 ^ (6 * j + 5) - 1 := by
  rw [← acceleratedOrbit_add, nSeq_step_three, climb_one]

/-- The peak is above the start, by a wide margin. -/
theorem nSeq_lt_peak (j : Nat) : 8 * aSeq j + 4 < 3 ^ (6 * j + 5) := by
  have hspec := aSeq_spec j
  have hA : 72 * aSeq j + 40 = 8 * 2 ^ (6 * j + 5) := by omega
  have hle : (2 : Nat) ^ (6 * j + 5) ≤ 3 ^ (6 * j + 5) :=
    Nat.pow_le_pow_left (by omega) _
  have h3 : (0 : Nat) < 3 ^ (6 * j + 5) := Nat.pow_pos (by omega)
  generalize (2 : Nat) ^ (6 * j + 5) = X at hA hle
  generalize (3 : Nat) ^ (6 * j + 5) = Y at hle h3 ⊢
  omega

/-- Every intermediate value of the climb, via `ScaleLadder.climb` at `E = 2^(k−i)`. -/
theorem climb_mid (k i : Nat) (hik : i ≤ k) :
    acceleratedOrbit i (2 ^ k - 1) = 3 ^ i * 2 ^ (k - i) - 1 := by
  have hsplit : (2 : Nat) ^ k = 2 ^ i * 2 ^ (k - i) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have h := ScaleLadder.climb i (2 ^ (k - i)) (Nat.pow_pos (by omega))
  rw [← hsplit] at h
  exact h

/-- **The orbit never falls below the start before the peak.**  Up to time
`6j + 8` the family is still at or above where it began. -/
theorem nSeq_no_drop_before_peak (j t : Nat) (ht : t ≤ 6 * j + 5 + 3) :
    nSeq j ≤ acceleratedOrbit t (nSeq j) := by
  have hspec := aSeq_spec j
  have hpk : (0 : Nat) < 2 ^ (6 * j + 5) := Nat.pow_pos (by omega)
  rcases Nat.lt_or_ge t 3 with hsmall | hbig
  · have h1 : acceleratedStep (8 * aSeq j + 3) = 12 * aSeq j + 5 := by
      rw [acceleratedStep, if_neg (by omega)]; omega
    have hcase : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases hcase with rfl | rfl | rfl
    · show nSeq j ≤ nSeq j
      omega
    · show nSeq j ≤ acceleratedStep (nSeq j)
      rw [show nSeq j = 8 * aSeq j + 3 from rfl, h1]
      omega
    · show nSeq j ≤ acceleratedStep (acceleratedStep (nSeq j))
      rw [show nSeq j = 8 * aSeq j + 3 from rfl, h1, acceleratedStep, if_neg (by omega)]
      omega
  · obtain ⟨i, rfl⟩ : ∃ i, t = i + 3 := ⟨t - 3, by omega⟩
    rw [← acceleratedOrbit_add, nSeq_step_three, climb_mid _ i (by omega)]
    have hge : (2 : Nat) ^ (6 * j + 5) ≤ 3 ^ i * 2 ^ (6 * j + 5 - i) := by
      have hsplit : (2 : Nat) ^ (6 * j + 5) = 2 ^ i * 2 ^ (6 * j + 5 - i) := by
        rw [← Nat.pow_add]; congr 1; omega
      have : (2 : Nat) ^ i ≤ 3 ^ i := Nat.pow_le_pow_left (by omega) _
      calc (2 : Nat) ^ (6 * j + 5) = 2 ^ i * 2 ^ (6 * j + 5 - i) := hsplit
        _ ≤ 3 ^ i * 2 ^ (6 * j + 5 - i) := Nat.mul_le_mul_right _ this
    show 8 * aSeq j + 3 ≤ _
    omega

/-- **No tail suffices at run length two.**  For every `B` there is an `n` with
`n % 8 = 3` — hence `r(n) = 2` — whose orbit has still not descended after `B`
steps.

Consequently there is no `s : ℕ → ℕ` with `T^(r(n) + s(r(n)))(n) < n` for every
odd `n > 1`: at run length `2` the required tail is unbounded. -/
theorem no_tail_at_run_length_two (B : Nat) :
    ∃ n : Nat, n % 8 = 3 ∧ n ≤ acceleratedOrbit B n :=
  ⟨nSeq B, nSeq_mod_eight B, nSeq_no_drop_before_peak B B (by omega)⟩

end RunLengthUnbounded
end Collatz
