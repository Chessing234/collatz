import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Xiangrui(王祥睿) Wang, "Exact Valuation Geometry and Root-Anchored Certificates for the Accelerated Collatz Map I Affine Height, Dyadic Normalization Ports, and Finite Inverse Words", 2026.

Title: Exact Valuation Geometry and Root-Anchored Certificates for the Accelerated Collatz Map I Affine Height, Dyadic Normalization Ports, and Finite Inverse Words

Abstract (from harvested metadata, truncated):
Let[U(n)=\operatorname{oddpart}(3n+1)]denote the accelerated Collatz map on the positive odd integers. An exact valuation word (w=(a_1,\ldots,a_K)), defined by[3n_{j-1}+1=2^{a_j}n_j,]determines the classical affine ledger[A_j=\sum_{i=1}^{j}a_i,\qquadC_w=\sum_{i=0}^{K-1}3^{K-1-i}2^{A_i},\qquad2^{A_K}n_K=3^Kn_0+C_w.] This paper reorganizes that finite identity into two distinct boundaries:[P_w=2^{A_K}-3^K,\qquadH_w(n_0)=C_w-P_wn_0,\qquad2^{A_K}(n_K-n_0)=H_w(n_0).]Thus multiplicative contraction and actual descent are not equivalent. The same distinction is obtained for finite windows ending inside the final dyadic tail, with shortcut-step length[J=A_{K-1}+\rho]and exact quantities[P^\partial=2...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22197748
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22197748

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Xiangrui(王祥睿) Wang, \"Exact Valuation Geometry and Root-Anchored Certificates for the Accelerated Collatz Map I Affine Height, Dyadic Normalization Ports, and Finite Inverse Words\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22197748 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_22197748
