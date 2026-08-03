import Lake
open Lake DSL

package Collatz where
  version := v!"0.1.0"
  keywords := #["Lean", "formalization", "AI", "Collatz"]

lean_lib Collatz where
  roots := #[`Collatz]
