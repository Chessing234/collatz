import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hassan Douzi, "Convergence of some perturbed sequences of rational powers and application to syracuse problem", arXiv:2205.12724 [2022].

Title: Convergence of some perturbed sequences of rational powers and application to syracuse problem

Abstract (from OpenAlex metadata, truncated):
Sequences of rational powers \left( ξ\left( \frac{p}{q} \right)^{n} \right)_{n\ge 0}, especially in the case \frac{p}{q}=\frac{3}{2}, have a connection with many important combinatorics and number theory problems as for example Syracuse, Z-number and waring problems. Conjectures from such problems are known to be intractable and only few partial results exist until now. In this paper, we study a family of perturbed sequences of rational powers called 'Branch sequences' of the form \left( S_{n}=\left( ξ+Σ_{n} \right)\left( \frac{p^{n}}{q^{n+e_{n}}} \right) \right)_{n\ge 0}. Under the assumption that such sequences are deterministic and they have controlled positive perturbations, we establish the convergence result: min_{n\ge 0}(S_{n})\le q^{2}. As an application, we show that Syracuse sequences are 'Branch sequences' with all the required conditions for convergence and therefore this con

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2205.12724
-/

namespace Collatz.Papers.Arxiv2205_12724

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hassan Douzi, \"Convergence of some perturbed sequences of rational powers and application to syracuse problem\", arXiv:2205.12724 [2022]."

/-- Recorded claim shell (structural); the paper's theorem is not proved.
Placeholder equals the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2205_12724
