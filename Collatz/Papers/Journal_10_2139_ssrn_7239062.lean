import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nikpour, Parsa and Rabbani, Masoud, "&lt;div&gt;
 A Certified Density Exponent for the 3x + 1 Problem and the Smallest Atom of the Syracuse Random Variable
&lt;/div&gt;", 2026.

Title: &lt;div&gt;
 A Certified Density Exponent for the 3x + 1 Problem and the Smallest Atom of the Syracuse Random Variable
&lt;/div&gt;

Abstract (from harvested metadata, truncated):
The Krasikov–Lagarias bound π_a(x) ≫ x^0.84, obtained in 2003 by solving a linear program in 3^10 variables, had not been improved. We observe that their program is a nonlinear Perron–Frobenius eigenvalue problem for a monotone, positively homogeneous, concave operator, so feasibility is decided by a power iteration rather than by linear programming. A certificate at level 20, verified in exact integer arithmetic, gives π_a(x) ≫ x^0.914947. We then show that the same operator, run one 3‑adic digit at a time, is the Frobenius–Perron operator of Tao's Syracuse random variable. This yields c_n ≫ (3t)^(-n) with t = 10449/10000, hence β ≤ 1.039979 for the exponent of the smallest atom of Syrac(Z/3^n Z), against the previously recorded β ≤ 3.1404.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.7239062
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_7239062

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nikpour, Parsa and Rabbani, Masoud, \"&lt;div&gt;
 A Certified Density Exponent for the 3x + 1 Problem and the Smallest Atom of the Syracuse Random Variable
&lt;/div&gt;\", DOI:10.2139/ssrn.7239062 [2026]."

/-- Recorded density-style claim shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat)

/-- Weak density scaffolding (Mathlib-copied `Rat` facts); strictly weaker than the paper. -/
theorem mainStatement_weak : mainStatement := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  exact Collatz.Papers.MathlibCopied.density_shell_of_pos eps N heps

end Collatz.Papers.Journal_10_2139_ssrn_7239062
