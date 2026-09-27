import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Maxwell C. Siegel, "The Collatz Conjecture & Non-Archimedean Spectral Theory - Part I - Arithmetic Dynamical Systems and Non-Archimedean Value Distribution Theory", 2024.

Title: The Collatz Conjecture & Non-Archimedean Spectral Theory - Part I - Arithmetic Dynamical Systems and Non-Archimedean Value Distribution Theory

Abstract (from harvested metadata, truncated):
Let $$q$$ be an odd prime, and let $$T_{q}:\mathbb{Z}\rightarrow\mathbb{Z}$$ be the Shortened $$qx+1$$ map, defined by $$T_{q}\left(n\right)=n/2$$ if $$n$$ is even and $$T_{q}\left(n\right)=\left(qn+1\right)/2$$ if $$n$$ is odd. The study of the dynamics of these maps is infamous for its difficulty, with the characterization of the dynamics of $$T_{3}$$ being an alternative formulation of the famous Collatz Conjecture. This series of papers presents a new paradigm for studying such arithmetic dynamical systems by way of a neglected area of ultrametric analysis which we have termed $$\left(p,q\right)$$ -adic analysis, the study of functions from the $$p$$ -adics to the $$q$$ -adics, where $$p$$ and $$q$$ are distinct primes. In this, the first paper, working with the $$T_{q}$$ maps as a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1134/s2070046624020055
-/

namespace Collatz.Papers.Journal_10_1134_s2070046624020055

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Maxwell C. Siegel, \"The Collatz Conjecture & Non-Archimedean Spectral Theory - Part I - Arithmetic Dynamical Systems and Non-Archimedean Value Distribution Theory\", P-Adic Numbers Ultrametric Analysis and Applications, DOI:10.1134/s2070046624020055 [2024]."

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

end Collatz.Papers.Journal_10_1134_s2070046624020055
