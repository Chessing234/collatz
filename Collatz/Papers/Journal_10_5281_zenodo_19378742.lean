import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Pablo  Nogueira Grossi, "The Collatz Conjecture as a Corollary of Crystal Geometry: A Supplement to the Principia Orthogona Crystal Paper", 2026.

Title: The Collatz Conjecture as a Corollary of Crystal Geometry: A Supplement to the Principia Orthogona Crystal Paper

Abstract (from harvested metadata, truncated):
Book III of the Principia Orthogona series (Nested Infinities) demonstrates that the generative operator chain G=U∘F∘K∘C G = U \circ F \circ K \circ C G=U∘F∘K∘C, the dm³ framework, and the crystal geometry encoded in the G6 Crystal are not mathematical constructs imposed on nature but translations of structures already visible in it. The semi-permanent polar vortex—most strikingly Saturn’s north-polar hexagon—is an empirically observable dm³ system that has crossed the monster threshold at stability parameter g6=33 g^6 = 33 g6=33: its hexagonal Chladni figure is the crystal math made visible at planetary scale. This supplement argues that the Collatz conjecture inhabits the same structure. The coefficient c=3 c = 3 c=3 in the rule 3n+1 3n + 1 3n+1 is not arbitrary; it is the fingerprint...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19378742
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19378742

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Pablo  Nogueira Grossi, \"The Collatz Conjecture as a Corollary of Crystal Geometry: A Supplement to the Principia Orthogona Crystal Paper\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19378742 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19378742
