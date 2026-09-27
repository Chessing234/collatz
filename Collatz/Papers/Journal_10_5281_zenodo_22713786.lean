import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for BIANCHET, ALESSANDRO, "COLLATZ - APPUNTI v.2", 2026.

Title: COLLATZ - APPUNTI v.2

Abstract (from harvested metadata, truncated):
Nel presente lavoro si analizza la mappa di Collatz accelerata agendo sulla rappresentazione binaria degli interi positivi. Si stabilisce un vincolo cinematico rigido sulla lunghezza massima m delle sequenze di espansione pura (ovvero iterazioni dispari consecutive con valutazione 2-adica unitaria, v2(3x + 1) = 1). Dimostriamo che per ogni intero dispari x0 ∈ N rappresentabile in esattamente N bit, la durata massima di una fase di espansione ininterrotta e limitata superiormente dalla costante universale log3 2: mmax(N) = ⌊(N − 1) · log3 2⌋ Tale risultato esprime la velocit`a di dissipazione della ”riserva informativa” dei bit di coda ed esclude la presenza di fasi di crescita esponenziale pura di durata arbitraria per interi di dimensione finita.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22713786
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22713786

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "BIANCHET, ALESSANDRO, \"COLLATZ - APPUNTI v.2\", DOI:10.5281/zenodo.22713786 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22713786
