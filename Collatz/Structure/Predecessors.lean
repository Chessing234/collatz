import Collatz.Core.Reach
import Collatz.Search.Sieved

/-!
# Going backwards: infinite families that provably reach one

Every positive result in this project so far is either brute force (`Search`) or
an obstruction (`Obstruction`, `SieveDensity`, `DensityRate`).  Nothing generates
new numbers known to reach `1` except by checking them one at a time.

The inverse of the odd step does exactly that.  If `3n + 1 = 2 ^ j · m` with
`j ≥ 1`, then `n` is odd, its first step is `3n + 1 = 2 ^ j · m`, and `j`
halvings land on `m`.  So

**`m` reaches `1` implies `n` reaches `1`** (`reachesOne_of_pred_odd`).

That is a generator.  Starting from `m = 1` it produces every `n` with
`3n + 1` a power of two — the family `1, 5, 21, 85, 341, …`, namely
`(4 ^ k − 1)/3` — each of which lands on a power of two in a single odd step and
then falls straight to `1`.  Starting from any number already known to reach `1`
it produces infinitely many more.

Combined with the verified range this is a genuine, if modest, positive result:
`Search` establishes a finite initial segment by computation, and the generator
lifts *every* member of it to an unbounded family, so the set of numbers proved
to reach `1` is infinite and unbounded rather than merely large.

None of this bears on the conjecture, since generating a sparse infinite family
is not the same as covering the integers.  But it is the only direction in the
project where new positive facts come from an argument rather than from a
search, and it is worth having the machinery on record.
-/

namespace Collatz
namespace Predecessors

open Reach

/-! ## The inverse odd step -/

/-- **The generator.**  If `3n + 1 = 2 ^ j · m` with `j ≥ 1` and `m` reaches `1`,
then `n` reaches `1`.  The single odd step from `n` lands on `2 ^ j · m`, and
powers of two divide out of reachability. -/
theorem reachesOne_of_pred_odd {n m j : Nat} (hn : 0 < n) (hj : 0 < j)
    (h : 3 * n + 1 = 2 ^ j * m) (hm : ReachesOne m) : ReachesOne n := by
  -- `3n + 1` is even, so `n` is odd
  have heven : (3 * n + 1) % 2 = 0 := by
    have h2 : (2:Nat) ^ j = 2 * 2 ^ (j - 1) := by
      have hsplit : j = (j - 1) + 1 := by omega
      rw [show (2:Nat) ^ j = 2 ^ ((j - 1) + 1) from by rw [← hsplit], Arith.two_pow_succ]
    rw [h, h2, Nat.mul_assoc]
    omega
  have hodd : n % 2 = 1 := by omega
  -- the step lands on `2 ^ j * m`
  have hstep : step n = 2 ^ j * m := by
    rw [step_odd hn hodd, h]
  refine (reachesOne_iff_step n).mpr ?_
  rw [hstep]
  exact (reachesOne_two_pow_mul_iff j m).mpr hm

/-- The special case `m = 1`: anything whose successor is a power of two reaches
`1`. -/
theorem reachesOne_of_three_mul_add_one_eq_two_pow {n j : Nat} (hn : 0 < n) (hj : 0 < j)
    (h : 3 * n + 1 = 2 ^ j) : ReachesOne n := by
  refine reachesOne_of_pred_odd hn hj ?_ reachesOne_one
  rw [h, Nat.mul_one]

/-! ## The explicit family `(4 ^ k − 1)/3` -/

/-- `fam k` is the `k`-th member of the family: `0, 1, 5, 21, 85, 341, …`. -/
def fam : Nat → Nat
  | 0 => 0
  | k + 1 => 4 * fam k + 1

/-- The defining property: `3 · fam k + 1 = 4 ^ k`. -/
theorem three_mul_fam_add_one (k : Nat) : 3 * fam k + 1 = 4 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hpow : (4:Nat) ^ (k + 1) = 4 * 4 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [fam, hpow, ← ih]
    omega

/-- `4 ^ k` is an even power of two. -/
theorem four_pow_eq (k : Nat) : (4:Nat) ^ k = 2 ^ (2 * k) := by
  rw [Nat.pow_mul]

/-- The family is positive from the first index on. -/
theorem fam_pos {k : Nat} (hk : 0 < k) : 0 < fam k := by
  cases k with
  | zero => omega
  | succ k => rw [fam]; omega

/-- **Every member of the family reaches one.**  A single odd step sends
`fam k` to `4 ^ k`, which is a power of two. -/
theorem reachesOne_fam {k : Nat} (hk : 0 < k) : ReachesOne (fam k) := by
  refine reachesOne_of_three_mul_add_one_eq_two_pow (j := 2 * k) (fam_pos hk) (by omega) ?_
  rw [three_mul_fam_add_one, four_pow_eq]

/-- The family grows: `fam (k+1) > fam k`, so it is unbounded. -/
theorem fam_lt_fam_succ (k : Nat) : fam k < fam (k + 1) := by
  rw [fam]
  omega

/-- Concretely, `fam k` is at least `k`, so the family exceeds every bound. -/
theorem le_fam : ∀ k : Nat, k ≤ fam k := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
    rw [fam]
    omega

/-- **An unbounded set of numbers proved to reach one**, obtained by an argument
rather than by search. -/
theorem exists_large_reachesOne (B : Nat) : ∃ n : Nat, B < n ∧ ReachesOne n := by
  refine ⟨fam (B + 1), ?_, reachesOne_fam (by omega)⟩
  have := le_fam (B + 1)
  omega

/-! ## Lifting the verified range

The generator applies to every number the search has already settled, not only
to `1`, so each verified value spawns its own unbounded family. -/

/-- **Every verified number lifts.**  For `m` below the verified bound and any
`j ≥ 1`, a solution `n` of `3n + 1 = 2 ^ j · m` reaches `1`. -/
theorem reachesOne_of_pred_verified {n m j : Nat} (hn : 0 < n) (hm : 0 < m)
    (hlt : m < 102400) (hj : 0 < j) (h : 3 * n + 1 = 2 ^ j * m) : ReachesOne n :=
  reachesOne_of_pred_odd hn hj h (Search.reachesOne_of_lt_102400 hm hlt)

/-- The generator composes with itself: two inverse odd steps in a row. -/
theorem reachesOne_of_pred_twice {n m p j i : Nat} (hn : 0 < n) (hp : 0 < p)
    (hj : 0 < j) (hi : 0 < i)
    (h1 : 3 * n + 1 = 2 ^ j * p) (h2 : 3 * p + 1 = 2 ^ i * m)
    (hm : ReachesOne m) : ReachesOne n :=
  reachesOne_of_pred_odd hn hj h1 (reachesOne_of_pred_odd hp hi h2 hm)

/-- The whole point, stated plainly: the set of numbers known to reach `1` is
closed under the inverse odd step, and therefore infinite. -/
theorem closed_under_pred :
    (∀ n m j : Nat, 0 < n → 0 < j → 3 * n + 1 = 2 ^ j * m → ReachesOne m → ReachesOne n) ∧
    (∀ B : Nat, ∃ n : Nat, B < n ∧ ReachesOne n) :=
  ⟨fun _ _ _ hn hj h hm => reachesOne_of_pred_odd hn hj h hm, exists_large_reachesOne⟩

end Predecessors
end Collatz
