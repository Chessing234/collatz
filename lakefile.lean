import Lake
open Lake DSL

package Cline where
  version := v!"0.1.0"
  keywords := #["Lean", "formalization", "AI", "conjecture"]

lean_lib Cline where
  roots := #[`Cline]
