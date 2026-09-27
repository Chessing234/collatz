import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Elias De Jesus, "Multiplier-Genericity in the Upper-Triangular Collatz Carry Cocycle: A u-Deformation Control for Realizer Zero-Run Rates", 2026.

Title: Multiplier-Genericity in the Upper-Triangular Collatz Carry Cocycle: A u-Deformation Control for Realizer Zero-Run Rates

Abstract (from harvested metadata, truncated):
This technical note records a controlled (u)-deformation of the accelerated (3x+1) carry cocycle. The Collatz multiplier (3) is replaced by an arbitrary odd unit (u) in the upper-triangular cocycle[M_u(d)=\begin{pmatrix}2^d & 1\0 & u\end{pmatrix},]producing the deformed carry[C_{u,D}=\sum_{j=0}^{L-1}u^{L-1-j}2^{S_j}.]The purpose of the deformation is not to define a new dynamical system, but to test whether realizer zero-run behavior is special to the Collatz multiplier (3) or generic across odd-unit (2)-adic carry cocycles. -\frac{1}{S}\log_2\Pr(E_{u,D}\ge \alpha S),]where (E_{u,D}) measures the leading high-bit zero-run length of the full-modulus realizer residue[x_{u,D}\equiv -u^{-L}C_{u,...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20987657
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20987657

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Elias De Jesus, \"Multiplier-Genericity in the Upper-Triangular Collatz Carry Cocycle: A u-Deformation Control for Realizer Zero-Run Rates\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20987657 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20987657
