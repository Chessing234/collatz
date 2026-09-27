import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Darrell Cox et al., "Generalizing Halbeisen's and Hungerbühler's optimal bounds for the length of Collatz cycles to 3 n + c cycles", 2021.

Title: Generalizing Halbeisen's and Hungerbühler's optimal bounds for the length of Collatz cycles to 3 n + c cycles

Abstract (from harvested metadata, truncated):
The next element in the $3n+1$ sequence is defined to be \((3n+1)/2\) if \(n\) is odd or \(n/2\) otherwise. The Collatz conjecture states that no matter what initial value of \(n\) is chosen, the sequence always reaches 1 (where it goes into the repeating sequence \((1,2,1,2,1,2,\ldots)\)). The only known Collatz cycle is \((1,2)\). Let \(c\) be an odd integer not divisible by \(3\). Similar cycles exist for the more general \(3n+c\) sequence. The \(3n+c\) cycles are commonly grouped according to their length and number of odd elements. The smallest odd element in one of these cycles is greater than the smallest odd elements of the other cycles in the group. A parity vector corresponding to a cycle consists of 0's for the even elements and 1's for the odd elements. A parity vector...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.22436/jmcs.024.04.05
-/

namespace Collatz.Papers.Journal_10_22436_jmcs_024_04_05

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Darrell Cox et al., \"Generalizing Halbeisen's and Hungerbühler's optimal bounds for the length of Collatz cycles to 3 n + c cycles\", Journal of Mathematics and Computer Science, DOI:10.22436/jmcs.024.04.05 [2021]."

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

end Collatz.Papers.Journal_10_22436_jmcs_024_04_05
