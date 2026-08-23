import Mathlib.Data.Nat.Defs
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The Mathlib attack branch — isolated from the no-Mathlib development

This directory is a **separate Lake project**.  The root `Collatz` library remains
Mathlib-free; nothing here is imported by it and nothing there is imported by this.
-/

namespace MathlibAttack

/-- The Collatz step. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The Syracuse (odd-to-odd) map: strip every factor of two from `3n+1`. -/
noncomputable def S (n : ℕ) : ℕ := (3 * n + 1) / 2 ^ (padicValNat 2 (3 * n + 1))

end MathlibAttack
