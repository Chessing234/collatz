import Collatz.Core.Reach
import Collatz.Search.Descent

/-!
# Predecessors and the backward tree

Everything so far pushes orbits *forward*.  This file works backwards: which
numbers step **to** a given `m`, and what does that say about which numbers
reach `1`?

The backward picture is simple to state.  A number `m` has the predecessor
`2m` always, and one further predecessor `(m−1)/3` exactly when `m ≡ 4 (mod 6)`.
Iterating the first option gives the powers-of-two tower already handled by
`reachesOne_two_pow_mul_iff`; combining the two options gives the *Collatz
tree* rooted at `1`, and the conjecture says the tree contains every positive
integer.

The most useful lemma proved here is `reachesOne_four_mul_add_one_iff`: for odd
`n`,

`4n + 1` reaches `1`  ↔  `n` reaches `1`.

It is useful because it is an *equivalence on odd numbers* — one of the few
available — and it generates an infinite family of numbers with known status
from each known number, in a direction the forward descent lemmas cannot reach.
-/

namespace Collatz
namespace Predecessor

open Reach

/-! ## Characterising one backward step -/

/-- Doubling is always a predecessor. -/
theorem step_two_mul {m : Nat} (hm : 0 < m) : step (2 * m) = m := by
  have h0 : 2 * m ≠ 0 := by omega
  have he : (2 * m) % 2 = 0 := by omega
  rw [step, if_neg h0, if_pos he]
  exact Nat.mul_div_cancel_left _ (by omega)

/-- When `m ≡ 4 (mod 6)` the number `(m−1)/3` is an odd predecessor of `m`. -/
theorem odd_pred_mod_six {m : Nat} (h : m % 6 = 4) : (m - 1) / 3 % 2 = 1 := by
  omega

/-- The odd predecessor really does step to `m`. -/
theorem step_odd_pred {m : Nat} (h : m % 6 = 4) : step ((m - 1) / 3) = m := by
  have hodd : (m - 1) / 3 % 2 = 1 := odd_pred_mod_six h
  have hpos : 0 < (m - 1) / 3 := by omega
  rw [step_odd hpos hodd]
  omega

/-- **Classification of predecessors.**  If `n` steps to a positive `m`, then
either `n = 2m`, or `n` is odd with `3n + 1 = m`. -/
theorem eq_of_step_eq {n m : Nat} (hn : 0 < n) (h : step n = m) :
    n = 2 * m ∨ (n % 2 = 1 ∧ 3 * n + 1 = m) := by
  rcases Arith.mod_two_eq_zero_or_one n with heven | hodd
  · left
    rw [step_even hn heven] at h
    omega
  · right
    refine ⟨hodd, ?_⟩
    rw [step_odd hn hodd] at h
    exact h

/-- An odd predecessor forces a congruence: if odd `n` steps to `m`, then
`m ≡ 4 (mod 6)`. -/
theorem mod_six_of_odd_step {n m : Nat} (hn : 0 < n) (hodd : n % 2 = 1)
    (h : step n = m) : m % 6 = 4 := by
  rw [step_odd hn hodd] at h
  omega

/-- A number not congruent to `4` modulo `6` has only the doubling
predecessor. -/
theorem eq_two_mul_of_step_eq {n m : Nat} (hn : 0 < n) (hm : m % 6 ≠ 4)
    (h : step n = m) : n = 2 * m := by
  rcases eq_of_step_eq hn h with hcase | ⟨hodd, heq⟩
  · exact hcase
  · exact absurd (mod_six_of_odd_step hn hodd h) hm

/-! ## Backward transfer of `ReachesOne` -/

/-- Doubling preserves and reflects reaching `1`. -/
theorem reachesOne_two_mul_iff' (m : Nat) : ReachesOne (2 * m) ↔ ReachesOne m :=
  reachesOne_two_mul_iff m

/-- The odd predecessor preserves and reflects reaching `1`. -/
theorem reachesOne_odd_pred_iff {m : Nat} (h : m % 6 = 4) :
    ReachesOne ((m - 1) / 3) ↔ ReachesOne m := by
  rw [reachesOne_iff_step ((m - 1) / 3), step_odd_pred h]

/-- **The `4n+1` equivalence.**  For odd `n`, the number `4n + 1` reaches `1`
exactly when `n` does. -/
theorem reachesOne_four_mul_add_one_iff {n : Nat} (hn : 0 < n) (hodd : n % 2 = 1) :
    ReachesOne (4 * n + 1) ↔ ReachesOne n := by
  have h1 : (4 * n + 1) % 2 = 1 := by omega
  have hpos : 0 < 4 * n + 1 := by omega
  rw [reachesOne_iff_step (4 * n + 1), step_odd hpos h1]
  have h2 : 3 * (4 * n + 1) + 1 = 2 ^ 2 * (3 * n + 1) := by
    have : (2:Nat) ^ 2 = 4 := by decide
    omega
  rw [h2, reachesOne_two_pow_mul_iff]
  exact (reachesOne_odd_iff hn hodd).symm

/-- The forward half of the `4n+1` equivalence. -/
theorem reachesOne_four_mul_add_one {n : Nat} (hn : 0 < n) (hodd : n % 2 = 1)
    (h : ReachesOne n) : ReachesOne (4 * n + 1) :=
  (reachesOne_four_mul_add_one_iff hn hodd).mpr h

/-- `4n + 1` is odd whenever `n` is, so the equivalence can be iterated. -/
theorem odd_four_mul_add_one (n : Nat) : (4 * n + 1) % 2 = 1 := by omega

/-- `4n + 1` is positive whenever `n` is. -/
theorem pos_four_mul_add_one (n : Nat) : 0 < 4 * n + 1 := by omega

/-- Iterating the map `n ↦ 4n + 1`. -/
def tower : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => 4 * tower k n + 1

/-- The base of the tower. -/
@[simp] theorem tower_zero (n : Nat) : tower 0 n = n := rfl

/-- One more storey of the tower. -/
theorem tower_succ (k n : Nat) : tower (k + 1) n = 4 * tower k n + 1 := rfl

/-- Every storey of the tower over an odd number is odd. -/
theorem odd_tower {n : Nat} (hodd : n % 2 = 1) (k : Nat) : tower k n % 2 = 1 := by
  induction k with
  | zero => exact hodd
  | succ k _ => rw [tower_succ]; omega

/-- Every storey of the tower over a positive number is positive. -/
theorem pos_tower {n : Nat} (hn : 0 < n) (k : Nat) : 0 < tower k n := by
  induction k with
  | zero => exact hn
  | succ k ih => rw [tower_succ]; omega

/-- The tower is strictly increasing above `0`. -/
theorem lt_tower_succ {n : Nat} (hn : 0 < n) (k : Nat) : tower k n < tower (k + 1) n := by
  have := pos_tower hn k
  rw [tower_succ]
  omega

/-- **An infinite family from every known value.**  If an odd `n` reaches `1`,
so does every storey of the tower `n, 4n+1, 16n+5, …`, and conversely. -/
theorem reachesOne_tower_iff {n : Nat} (hn : 0 < n) (hodd : n % 2 = 1) (k : Nat) :
    ReachesOne (tower k n) ↔ ReachesOne n := by
  induction k with
  | zero => rw [tower_zero]
  | succ k ih =>
    rw [tower_succ,
      reachesOne_four_mul_add_one_iff (pos_tower hn k) (odd_tower hodd k), ih]

/-- The tower over `1` consists of numbers that reach `1`: `1, 5, 21, 85, …`. -/
theorem reachesOne_tower_one (k : Nat) : ReachesOne (tower k 1) :=
  (reachesOne_tower_iff (by omega) (by omega) k).mpr reachesOne_one

/-- The tower over `3` consists of numbers that reach `1`: `3, 13, 53, 213, …`. -/
theorem reachesOne_tower_three (k : Nat) : ReachesOne (tower k 3) :=
  (reachesOne_tower_iff (by omega) (by omega) k)
    |>.mpr (Search.reachesOne_of_le_10000 (by omega) (by omega))

/-- The tower over `7` consists of numbers that reach `1`. -/
theorem reachesOne_tower_seven (k : Nat) : ReachesOne (tower k 7) :=
  (reachesOne_tower_iff (by omega) (by omega) k)
    |>.mpr (Search.reachesOne_of_le_10000 (by omega) (by omega))

/-- The tower over `27` consists of numbers that reach `1`. -/
theorem reachesOne_tower_twentyseven (k : Nat) : ReachesOne (tower k 27) :=
  (reachesOne_tower_iff (by omega) (by omega) k)
    |>.mpr (Search.reachesOne_of_le_10000 (by omega) (by omega))

/-- A counterexample cannot be of the form `4n + 1` with `n` odd and `n`
already known to reach `1`. -/
theorem not_counterexample_four_mul_add_one {n : Nat} (hn : 0 < n) (hodd : n % 2 = 1)
    (h : ReachesOne n) : ReachesOne (4 * n + 1) :=
  reachesOne_four_mul_add_one hn hodd h

/-- A minimal counterexample is not one more than four times a smaller odd
number, because that smaller number reaches `1` by minimality. -/
theorem minimal_not_four_mul_add_one {n m : Nat}
    (hmin : ∀ j : Nat, 0 < j → j < n → ReachesOne j) (hnr : ¬ ReachesOne n)
    (hm : 0 < m) (hmodd : m % 2 = 1) (heq : n = 4 * m + 1) : False := by
  have hlt : m < n := by omega
  exact hnr (heq ▸ reachesOne_four_mul_add_one hm hmodd (hmin m hm hlt))

/-! ## Predecessor sets -/

/-- `IsPredecessor n m` says `n` steps directly to `m`. -/
def IsPredecessor (n m : Nat) : Prop := step n = m

/-- Doubling gives a predecessor of every positive number. -/
theorem isPredecessor_two_mul {m : Nat} (hm : 0 < m) : IsPredecessor (2 * m) m :=
  step_two_mul hm

/-- The odd predecessor exists exactly in the class `4 mod 6`. -/
theorem isPredecessor_odd_pred {m : Nat} (h : m % 6 = 4) :
    IsPredecessor ((m - 1) / 3) m :=
  step_odd_pred h

/-- A positive number has at most the two predecessors described above. -/
theorem isPredecessor_cases {n m : Nat} (hn : 0 < n) (h : IsPredecessor n m) :
    n = 2 * m ∨ (n % 2 = 1 ∧ 3 * n + 1 = m) :=
  eq_of_step_eq hn h

/-- A predecessor of a number that reaches `1` reaches `1`. -/
theorem reachesOne_of_isPredecessor {n m : Nat} (h : IsPredecessor n m)
    (hm : ReachesOne m) : ReachesOne n :=
  reachesOne_of_step (by rw [IsPredecessor] at h; rw [h]; exact hm)

/-- Numbers congruent to `2` modulo `3` have no odd predecessor, so their only
predecessor is the double. -/
theorem no_odd_predecessor_of_mod_three {n m : Nat} (hn : 0 < n) (hm : m % 3 = 2)
    (h : IsPredecessor n m) : n = 2 * m := by
  refine eq_two_mul_of_step_eq hn (fun hc => ?_) h
  omega

end Predecessor
end Collatz
