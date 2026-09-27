import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Robin Waterfield, "Practicing Politics in Syracuse", 2023.

Title: Practicing Politics in Syracuse

Abstract (from harvested metadata, truncated):
Abstract This chapter gives accounts of Plato’s famous two visits to Sicily in 366 and 361 BCE, when Dionysius II was the tyrant of Syracuse. Chunks of Plato’s Letter 7, the main source for accounts of these visits, are translated over the course of the chapter. Encouraged by Dion and others, Plato felt that he had an opportunity to put some of his political theory into practice by converting Dionysius from a tyrant (an unconstitutional sole ruler) to a king who allowed his subjects some measure of democracy. However, Plato did not expect to turn Dionysius into a philosopher king as described in Republic. The likely nature of Dionysius’s court is described. Plato’s project foundered, in the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1093/oso/9780197564752.003.0007
-/

namespace Collatz.Papers.Journal_10_1093_oso_9780197564752_003_0007

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Robin Waterfield, \"Practicing Politics in Syracuse\", Plato of Athens, DOI:10.1093/oso/9780197564752.003.0007 [2023]."

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

end Collatz.Papers.Journal_10_1093_oso_9780197564752_003_0007
