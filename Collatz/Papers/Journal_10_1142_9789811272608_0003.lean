import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nicola Fabiano et al., "Collatz Hypothesis and Kurepa’s Conjecture", 2023.

Title: Collatz Hypothesis and Kurepa’s Conjecture

Abstract (from harvested metadata, truncated):
We discuss and give some insights on the Collatz conjecture, known as 3N + 1, and Kurepa’s hypothesis on the left factorial. First, the Collatz conjecture is considered and the density of values is compared to Planck’s black body radiation in physics, showing a remarkable agreement between the two. We also briefly discuss a generalization of Collatz conjecture for a generic sequence qN +1 by means of numerical analysis. Then, we give a brief historical excursus and prove in a simple way some properties of Kurepa’s function, also called the left factorial. We introduce Kurepa’s hypothesis, propose a new description, and the relation to Bezout’s parameters and the Diophantine equation. A numerical analysis supports Kurepa’s hypothesis and the conjecture about distribution for Kurepa’s...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1142/9789811272608_0003
-/

namespace Collatz.Papers.Journal_10_1142_9789811272608_0003

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nicola Fabiano et al., \"Collatz Hypothesis and Kurepa’s Conjecture\", WORLD SCIENTIFIC eBooks, DOI:10.1142/9789811272608_0003 [2023]."

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

end Collatz.Papers.Journal_10_1142_9789811272608_0003
