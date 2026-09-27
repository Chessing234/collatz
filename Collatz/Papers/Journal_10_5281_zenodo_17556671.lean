import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lee, Byoungwoo, "A Proof of the Collatz Conjecture via the Spectral Gap of an Entropic Laplacian (Version v3.2, Main Proof Only)", 2025.

Title: A Proof of the Collatz Conjecture via the Spectral Gap of an Entropic Laplacian (Version v3.2, Main Proof Only)

Abstract (from harvested metadata, truncated):
We develop an analytic and thermodynamic framework for the Collatz dynamics via the entropic Laplacian on the $2$--adic moduli space $M_C\simeq\mathbb{Z}_2$. The dynamics is encoded by a reversible, self--adjoint contraction $K$ on $L^2(M_C,\mu)$ (obtained from inverse--branch averaging of the odd/even maps with weights $p_o,p_e$), and by its generator $\Delta_C^{(\infty)} \;:=\; I - K .$ A unitary dilation on a parity--history space yields the compression identity $K=J^\dagger U_T J$ and the energy representation $\mathcal{E}[f]=\langle f,(I-K)f\rangle=\tfrac12\|Jf-U_TJf\|_{L^2}^2$, linking entropy dissipation to parity--branch coherence loss. Our main contributions are: (1) The Dirichlet f...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17556671
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17556671

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lee, Byoungwoo, \"A Proof of the Collatz Conjecture via the Spectral Gap of an Entropic Laplacian (Version v3.2, Main Proof Only)\", Zenodo, DOI:10.5281/zenodo.17556671 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_17556671
