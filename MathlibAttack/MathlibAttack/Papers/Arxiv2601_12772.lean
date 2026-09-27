import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Madhav Dhiman and Rohan Pandey, "Logical Undefinability of the Generalized Collatz Transition Relation in Büchi Arithmetic", arXiv:2601.12772 [2026].

Title: Logical Undefinability of the Generalized Collatz Transition Relation in Büchi Arithmetic

Abstract (truncated):
Let $q$ be an odd prime and let $d$ be an odd integer. We show that the arbitrary-step transition relation of the generalized Collatz map $T_{q,d}$ is not first-order definable in Base-2 Büchi Arithmetic ($BA_2$). We do this by demonstrating that if the transition relation were definable, the exponential set $P_q = \{q^y : y \in \mathbb{N}\}$ would also be definable in $BA_2$. Since $P_q$ is strictly non-semilinear, this yields a direct contradiction with the Cobham--Semënov theorem. Consequently, we demonstrate that no finite automaton reading base-2 representations can recognize this transition relation.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2601.12772
-/

namespace MathlibAttack.Papers.Arxiv2601_12772

open MathlibAttack.Papers

def citation : String := "Madhav Dhiman and Rohan Pandey, \"Logical Undefinability of the Generalized Collatz Transition Relation in B\u00fcchi Arithmetic\", arXiv:2601.12772 [2026]."

/-- Recorded claim shell (generalization); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2601_12772
