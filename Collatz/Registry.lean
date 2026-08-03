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

/-- Registry entries known to Lean. -/
def registry : List LemmaDraft :=
  [seedDraft]

/-- The registry is nonempty. -/
theorem registry_nonempty : registry ≠ [] := by
  decide

end Collatz
