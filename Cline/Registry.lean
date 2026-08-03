/-!
A tiny registry for paper-derived lemma drafts.
-/

import Cline.Basic

namespace Cline

/-- The first registry entry: the project goal itself. -/
def seedDraft : LemmaDraft where
  name := "cline_conjecture_shell"
  source := "project seed"
  statement := "Every orbit reaches 1, after the formal system is fixed."
  status := "open"

/-- Registry entries known to Lean. -/
def registry : List LemmaDraft :=
  [seedDraft]

/-- The registry is nonempty. -/
theorem registry_nonempty : registry ≠ [] := by
  decide

end Cline
