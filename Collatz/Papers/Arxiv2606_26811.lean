import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Weicheng Fu et al., "Emergence of Gamma-Type Upward-Phase Statistics in the Collatz Map: An Effective Poisson Process Mechanism", arXiv:2606.26811 [2026].

Title: Emergence of Gamma-Type Upward-Phase Statistics in the Collatz Map: An Effective Poisson Process Mechanism

Abstract (from OpenAlex metadata, truncated):
The Collatz map is a simple deterministic transformation whose orbit structure remains highly nontrivial. A recent direction-phase decomposition partitions each orbit into upward and downward steps, and numerical observations indicate that the number of upward phases, $N_{\uparrow}$, follows an approximate Gamma distribution. In this work, we provide a mechanistic explanation for this statistical regularity by modeling the occurrence of upward phases in the odd-compressed, or Syracuse, version of the Collatz map as a homogeneous Poisson process. From the mean-field logarithmic balance and the geometric distribution of $2$-adic valuations, we derive closed-form expressions for the Gamma parameters: the scale parameter $θ= 2/(2-\log_2 3)^2 \approx 11.61$ is constant, whereas the shape parameter $K$ grows logarithmically with the maximal initial value $X_0=2L+1$. We also analyze the closure conditions for periodic orbits, showing that nontrivial cycles are severely constrained, which supp

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2606.26811
-/

namespace Collatz.Papers.Arxiv2606_26811

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Weicheng Fu et al., \"Emergence of Gamma-Type Upward-Phase Statistics in the Collatz Map: An Effective Poisson Process Mechanism\", arXiv:2606.26811 [2026]."

/-- Recorded main claim shell (cycle); not proved.
States that any accelerated return to `n > 1` has already visited `1`. -/
def mainStatement : Prop :=
  ∀ n : Nat, n > 1 → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial 1-cycle returns to 1. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩


end Collatz.Papers.Arxiv2606_26811
