import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Seyma Yaman Kayadibi, "Exact and Delayed Descent in Accelerated Odd Collatz Spines with AAS-Based Metamorphic Separation", 2026.

Title: Exact and Delayed Descent in Accelerated Odd Collatz Spines with AAS-Based Metamorphic Separation

Abstract (from harvested metadata, truncated):
&lt;p&gt;This paper studies exact and delayed first-descent behavior in modular resistance spines for the accelerated odd Collatz map on positive odd integers. For spine elements of the form n = 2^m q − 1, the persistence identity shows that no descent below the initial value can occur before the m-th accelerated odd iterate. The paper identifies an explicit valuation threshold that converts this forced pre-descent delay into an exact first-descent certificate for an infinite certified residue subclass inside each spine.&lt;/p&gt; &lt;p&gt;The complementary non-certified residue classes are analyzed through shifted residues. The first-exit valuation in each shifted class is shown to be exact...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.7069138
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_7069138

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Seyma Yaman Kayadibi, \"Exact and Delayed Descent in Accelerated Odd Collatz Spines with AAS-Based Metamorphic Separation\", DOI:10.2139/ssrn.7069138 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_2139_ssrn_7069138
