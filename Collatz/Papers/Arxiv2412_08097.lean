import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fu, Weicheng, Wang, Yisen, "The Structure of the Route to the Period-three Orbit in the Collatz Map", arXiv:2412.08097 [2024].

Title: The Structure of the Route to the Period-three Orbit in the Collatz Map

Abstract (from OpenAlex metadata, truncated):
This study analyzes the Collatz map through nonlinear dynamics. By embedding integers in Sharkovsky's ordering, we show that odd initial values suffice for full dynamical characterization. We introduce ``direction phases'' to partition iterations into upward and downward phases, and derive a recursive function family parameterized by upward phase counts. Consequently, a logarithmic scaling law between iteration steps and initial values is revealed, demonstrating finite-time convergence to the period-three orbit. Moreover, we establish the equivalence of the Collatz map to a binary shift map, whose ergodicity guarantees universal convergence to attractors, providing additional support for convergence. Furthermore, we identify that basins of attraction follow power-law distributions and find that odd numbers classified by upward phases follow Gamma statistics. These results offer valuable 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2412.08097
-/

namespace Collatz.Papers.Arxiv2412_08097

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fu, Weicheng and Wang, Yisen, \"The Structure of the Route to the Period-three Orbit in the Collatz Map\", arXiv:2412.08097 [2024]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2412_08097
