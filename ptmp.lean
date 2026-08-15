def bits : Nat → Nat
  | 0 => 0
  | n + 1 => bits ((n + 1) / 2) + 1
decreasing_by omega

example : bits 1 = 1 := by decide
example : bits 27 = 5 := by decide
example : bits 3 = 2 := by decide
