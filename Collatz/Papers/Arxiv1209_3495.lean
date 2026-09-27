import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Laarhoven, Thijs, de Weger, Benne, "The Collatz conjecture and De Bruijn graphs", arXiv:1209.3495 [2012].

Title: The Collatz conjecture and De Bruijn graphs

Abstract (from OpenAlex metadata, truncated):
We study variants of the well-known Collatz graph, by considering the action of the 3n+1 function on congruence classes. For moduli equal to powers of 2, these graphs are shown to be isomorphic to binary De Bruijn graphs. Unlike the Collatz graph, these graphs are very structured, and have several interesting properties. We then look at a natural generalization of these finite graphs to the 2-adic integers, and show that the isomorphism between these infinite graphs is exactly the conjugacy map previously studied by Bernstein and Lagarias. Finally, we show that for generalizations of the 3n+1 function, we get similar relations with 2-adic and p-adic De Bruijn graphs.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1209.3495
-/

namespace Collatz.Papers.Arxiv1209_3495

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Laarhoven, Thijs and de Weger, Benne, \"The Collatz conjecture and De Bruijn graphs\", arXiv:1209.3495 [2012]."

/-- Recorded main claim shell (generalization); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv1209_3495
