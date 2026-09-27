import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Amor Boulouma, "The Generalized Collatz Conjecture: A Family of Maps H p (n) = strip&amp;lt;p(pn + 1)", 2026.

Title: The Generalized Collatz Conjecture: A Family of Maps H p (n) = strip&amp;lt;p(pn + 1)

Abstract (from harvested metadata, truncated):
&lt;div&gt; &lt;div&gt; We introduce a one-parameter family of maps generalizing the accelerated Collatz map: &lt;/div&gt; &lt;div&gt; Hp(n) = strip&amp;lt;p(pn + 1), &lt;/div&gt; &lt;div&gt; where strip&amp;lt;p removes all prime factors strictly less than p, and the domain is the set of p-rough &lt;/div&gt; &lt;div&gt; integers. For p = 3, this reduces to the standard accelerated Collatz map. &lt;/div&gt; &lt;div&gt; We state the generalized Collatz conjecture: for every p ≥ 3, every trajectory of Hp eventually &lt;/div&gt; &lt;div&gt; reaches the fixed point 1, except possibly for finitely many exceptional moduli that admit nontrivial cycles. &lt;/div&gt; &lt;div&gt; We report computation...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.7180198
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_7180198

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Amor Boulouma, \"The Generalized Collatz Conjecture: A Family of Maps H p (n) = strip&amp;lt;p(pn + 1)\", DOI:10.2139/ssrn.7180198 [2026]."

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

end Collatz.Papers.Journal_10_2139_ssrn_7180198
