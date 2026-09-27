import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Antoine Couet and Moonshot AI / Kimi K 2.6 Thinking, "Conditional Foster-Lyapunov Criterion for 2-adic Maps : From Collatz to the a=4 Threshold", 2026.

Title: Conditional Foster-Lyapunov Criterion for 2-adic Maps : From Collatz to the a=4 Threshold

Abstract (from harvested metadata, truncated):
**Description (English) :** This preprint establishes a conditional framework for the analysis of Collatz-type 2-adic iterations. We show that for iterative systems defined by $T_a : n \mapsto (an+1)/2^{v_2(an+1)}$ with odd $a$, the altitude function $V(n) = \log_2(n)$ is a Foster-Lyapunov function whose mean logarithmic drift per cycle is $\mu(a) = \log_2(a) - 2$. A universal critical threshold $a = 4$ follows: under an exponential mixing hypothesis for the 2-adic valuations, the system is positively recurrent (convergent) if $a < 4$ and transient (divergent) if $a > 4$. For the case $a = 3$ (the Syracuse / $3x+1$ problem), this implies conditional convergence to the trivial cycle $1 \to 4...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20613124
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20613124

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Antoine Couet and Moonshot AI / Kimi K 2.6 Thinking, \"Conditional Foster-Lyapunov Criterion for 2-adic Maps : From Collatz to the a=4 Threshold\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20613124 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20613124
