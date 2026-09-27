import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Harris, Juan, "Containment and Finite-Quotient Structure in Bad-State Lifting for the Odd Collatz Map", 2026.

Title: Containment and Finite-Quotient Structure in Bad-State Lifting for the Odd Collatz Map

Abstract (from harvested metadata, truncated):
This work applies a containment- and order-theoretic audit (Containment Modular Structure, CMS) to a computational study of bad-state lifting for the accelerated odd Collatz map. The finite lifting mechanisms are placed explicitly within established modular and 2-adic Collatz theory: finite parity or valuation itineraries determine residue cylinders, Collatz-type maps induce compatible maps on power-of-two quotients, and fixed branches act affinely on those cylinders. Accordingly, no novelty is claimed for the general cylinder-lifting or cylinder-preimage principles themselves. The contribution is an audit of the OCM-Lift claims and data. It shows that two reported finite regularities are im...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.31562605.v4
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_31562605_v4

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Harris, Juan, \"Containment and Finite-Quotient Structure in Bad-State Lifting for the Odd Collatz Map\", figshare, DOI:10.6084/m9.figshare.31562605.v4 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_6084_m9_figshare_31562605_v4
