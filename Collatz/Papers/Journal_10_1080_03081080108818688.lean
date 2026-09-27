import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Roger Zarnowski, "Generalized inverses and the total stopping times of collatz sequences", 2001.

Title: Generalized inverses and the total stopping times of collatz sequences

Abstract (from harvested metadata, truncated):
Let f(n) be defined on the set N is even, and f(n)=3n+1 if nie: is odd. A well-known conjecture in number theory asserts that for every n the sequence of iterates eventually reaches the cycle (4,2,1). We recast the conjecture in terms of a denumerable Markov chain with transition matrix P. Assuming that (4,2,1) is the only cycle, but allowing for the possibility of unbounded trajectories, we establish the complete structure of a particular generalized inverse X of I−P and show that the entries of X describe the trajectories and "total stopping times" of integers n. Moreover, the infinite matrix X satisfies properties which, in the case of finite matrices, are the defining properties of the unique group generalized inverse (I−P)#. The result extends to dynamical systems on ℕ consisting of...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1080/03081080108818688
-/

namespace Collatz.Papers.Journal_10_1080_03081080108818688

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Roger Zarnowski, \"Generalized inverses and the total stopping times of collatz sequences\", Linear and Multilinear Algebra, DOI:10.1080/03081080108818688 [2001]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_1080_03081080108818688
