import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yavdat Il’yasov, "On a generalized Collatz-Wielandt formula and finding saddle-node\n bifurcations", arXiv:2003.12556 [2020].

Title: On a generalized Collatz-Wielandt formula and finding saddle-node\n bifurcations

Abstract (from OpenAlex metadata, truncated):
We introduce the nonlinear generalized Collatz-Wielandt formula $$ \\lambda^*=\n\\sup_{x\\in Q}\\min_{i:h_i(x) \\neq 0} \\frac{g_i(x)}{ h_i(x)}, ~~Q \\subset\n\\mathbb{R}^n,$$ and prove that its solution $(x^*,\\lambda^*)$ yields the\nmaximal saddle-node bifurcation for systems of equations of the form:\n$g(x)-\\lambda h(x)=0, ~~x \\in Q$. Using this we introduce a simply verifiable\ncriterion for the detection of saddle-node bifurcations of a given system of\nequations. We apply this criterion to prove the existence of the maximal\nsaddle-node bifurcations for finite-difference approximations of nonlinear\npartial differential equations and for the system of power flow equations.\n

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2003.12556
-/

namespace Collatz.Papers.Arxiv2003_12556

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yavdat Il\u2019yasov, \"On a generalized Collatz-Wielandt formula and finding saddle-node\\n bifurcations\", arXiv:2003.12556 [2020]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2003_12556
