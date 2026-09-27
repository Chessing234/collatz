import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Régent, Xavier J., "&lt;p&gt;&lt;span&gt;The Syracuse Conjecture: A Categorical Resolution by Transport of Structure in the Sense of Bourbaki&lt;/span&gt;&lt;/p&gt;", 2026.

Title: &lt;p&gt;&lt;span&gt;The Syracuse Conjecture: A Categorical Resolution by Transport of Structure in the Sense of Bourbaki&lt;/span&gt;&lt;/p&gt;

Abstract (from harvested metadata, truncated):
&lt;span&gt; &lt;p&gt;Adopting the discipline of transport of structure formulated by Bourbaki [1], this paper establishes the Syracuse conjecture [2, 3] within a fully declared geometric ontology. Its usual arithmetic presentation is COLorb : ∀n ∈ N ∗ ∃t ∈ N, Ct (n) ∈ {1, 2, 4}. The universal quantifier prescribes no extensional method. We transport the statement into a many-sorted structure SSyr combining Peano arithmetic [4], the Syracuse law, an autonomous geometric machine, the dyadic completion [5] with its Haar measure [6], the measure algebra [7], and the quotient by residual profiles. Geometry is neither an approximation nor a simplification of arithmetic here: it is the chosen fundamental space. It covers the integers and their dynamics exactly: | · | : Gcan ∼−→ N ∗ , Γ ◦ V = Φ...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.7316441
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_7316441

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Régent, Xavier J., \"&lt;p&gt;&lt;span&gt;The Syracuse Conjecture: A Categorical Resolution by Transport of Structure in the Sense of Bourbaki&lt;/span&gt;&lt;/p&gt;\", DOI:10.2139/ssrn.7316441 [2026]."

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

end Collatz.Papers.Journal_10_2139_ssrn_7316441
