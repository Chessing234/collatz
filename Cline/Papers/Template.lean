/-!
Template for formalizing a paper.

Copy this file when adding a source.
Keep unproved claims as `def ... : Prop` until proved.
Do not use `axiom`, `admit`, or `sorry`.
-/

import Cline.Basic

namespace Cline.Papers.Template

/-- Replace with the exact bibliographic citation. -/
def citation : String := "Author, title, venue, year"

/-- Replace with the paper's main extracted statement. -/
def mainStatement : Prop := True

/-- A checked example proof. -/
theorem mainStatement_trivial : mainStatement := by
  trivial

end Cline.Papers.Template
