import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Taha Muhammad, "Taha's 2nd Solution of Collatz Sequence", 2024.

Title: Taha's 2nd Solution of Collatz Sequence

Abstract (from harvested metadata, truncated):
Abstract of Taha's 2nd Solution of Collatz Sequence let Collatz Sequence of (r)=S(r) let Collatz Sequence loop of (r)=lS(r) S(n)={(n/2)=k≤n-1,…,(h) or…},n∈N_even,k,h∈N_+⋯Fact 1 S(n)={(n/2)or (3n+1),…}⇒S(n)⊇S((n/2) or (3n+1) ),n∈N_+⋯Fact 2 ⇒ lS(n)= lS((n/2) or (3n+1) )…Fact 3 Example: S(5)={16,8,4,2,1}⇒ ∴S(5)⊇S(16)⊇S(8)⊇S(4)⊇S(2)⊇ S(1)…Fact 1⇒ lS(5)=lS(16)=lS(8)=lS(4)=lS(2)=lS(1)…Fact 2

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2024-f4j0z-v3
-/

namespace Collatz.Papers.Journal_10_33774_coe_2024_f4j0z_v3

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Taha Muhammad, \"Taha's 2nd Solution of Collatz Sequence\", DOI:10.33774/coe-2024-f4j0z-v3 [2024]."

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

end Collatz.Papers.Journal_10_33774_coe_2024_f4j0z_v3
