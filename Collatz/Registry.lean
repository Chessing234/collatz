import Collatz.Basic

/-!
A tiny registry for paper-derived lemma drafts.
-/

namespace Collatz

/-- The first registry entry: the project goal itself. -/
def seedDraft : LemmaDraft where
  name := "collatz_conjecture_shell"
  source := "project seed"
  statement := "Every positive orbit reaches 1."
  status := "open"

/-- A sourced bibliography entry for the accelerated 3x+1 formulation. -/
def lagarias2003BibliographyDraft : LemmaDraft where
  name := "lagarias_2003_three_x_plus_one_conjecture"
  source := "Jeffrey C. Lagarias, The 3x+1 problem: An annotated bibliography (1963--1999) (sorted by author), arXiv:math/0309224 [math.NT]."
  statement := "For every positive integer n > 1, the forward orbit under T(n) = (3n+1)/2 for odd n and T(n) = n/2 for even n includes 1."
  status := "open"

/-- Registry entries known to Lean. -/
def registry : List LemmaDraft :=
  [seedDraft, lagarias2003BibliographyDraft]

/-- The registry is nonempty. -/
theorem registry_nonempty : registry ≠ [] := by
  decide

end Collatz
