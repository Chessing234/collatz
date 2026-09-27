import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Benyamin Khanzadeh Holasou, "Collatz mapping on $\mathbb{Z}/10\mathbb{Z}$", 2021.

Title: Collatz mapping on $\mathbb{Z}/10\mathbb{Z}$

Abstract (from harvested metadata, truncated):
We introduce the \emph{Collatz conjecture} and its history. Some definition that this conjecture has, will be expressed and with these we try to explain some good lemma to justify the main properties of the \emph{Collatz conjecture}. With these lemmas a situation made to go through to write some mainly properties of Collatz graph on $\mathbb{Z}/10\mathbb{Z}$. Then with something provided it will go to draw the graph on $\mathbb{Z}/10\mathbb{Z}$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.48550/arxiv.2102.02650
-/

namespace Collatz.Papers.Journal_10_48550_arxiv_2102_02650

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Benyamin Khanzadeh Holasou, \"Collatz mapping on $\\mathbb{Z}/10\\mathbb{Z}$\", arXiv (Cornell University), DOI:10.48550/arxiv.2102.02650 [2021]."

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

end Collatz.Papers.Journal_10_48550_arxiv_2102_02650
