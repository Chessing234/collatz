import Collatz.Exploration.ExponentSearch

/-!
# Efficiently raising a matching exponent beyond an affine size bound

A modular exponent from the finite search may give a power that is too small
for a nonnegative affine index. Raise it by a multiple of the complete period.
The chosen jump uses binary length rather than the numerical size of the bound;
this avoids constructing an unnecessarily enormous power of two.

If the original power is already large enough it is retained exactly. Otherwise
one jump is sufficient, preserves its residue, and produces a strict size bound.
-/
namespace Collatz.Exploration.ExponentRaise

open ExponentSearch ThreePowerUnits ThreePowerLift

/-- A computable binary exponent strictly above a natural value. -/
def bitLength (S : Nat) : Nat := S.log2+1

/-- The chosen binary length works also at zero. -/
theorem below_bitLength (S : Nat) : S < (2:Nat)^(bitLength S) := by
  by_cases hz : S = 0
  · subst S; decide
  · exact (Nat.log2_lt hz).mp (by dsimp [bitLength]; omega)

/-- Keep a sufficient power; otherwise jump by a whole number of periods. -/
def raiseExponent (a e S : Nat) : Nat :=
  if S < (2:Nat)^e then e
  else e+periodLength a*(bitLength S/periodLength a+1)

/-- Raising never lowers the exponent. -/
theorem raise_ge (a e S : Nat) : e ≤ raiseExponent a e S := by
  unfold raiseExponent
  split <;> omega

/-- The raised power strictly exceeds the requested bound. -/
theorem raised_power_large (a e S : Nat) : S < (2:Nat)^(raiseExponent a e S) := by
  unfold raiseExponent
  split
  · assumption
  · have hp := periodLength_positive a
    have hd := Nat.div_add_mod (bitLength S) (periodLength a)
    have hr := Nat.mod_lt (bitLength S) hp
    have hmul : periodLength a*(bitLength S/periodLength a+1) =
        periodLength a*(bitLength S/periodLength a)+periodLength a := by
      rw [Nat.mul_add, Nat.mul_one]
    have he : bitLength S ≤ e+periodLength a*(bitLength S/periodLength a+1) := by omega
    exact Nat.lt_of_lt_of_le (below_bitLength S)
      (Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) he)

/-- The period jump preserves the residue at every ternary modulus. -/
theorem raised_power_residue (a e S : Nat) :
    (2:Nat)^(raiseExponent a e S)%3^a = (2:Nat)^e%3^a := by
  unfold raiseExponent
  split
  · rfl
  · cases a with
    | zero => simp [Nat.mod_one]
    | succ j =>
      have hq : 1 < (3:Nat)^(j+1) := by
        have h := Nat.pow_le_pow_right (by decide : 0 < (3:Nat)) (show 1 ≤ j+1 by omega)
        have hval : (3:Nat)^1 = 3 := rfl
        omega
      have hp : periodLength (j+1) = 2*3^j := by simp [periodLength]
      rw [power_period_shift _ _ _ _ hq (by rw [hp]; exact period_mod j)]

/-- A power that is already sufficient incurs no jump. -/
theorem keep_sufficient {a e S : Nat} (h : S < (2:Nat)^e) : raiseExponent a e S = e := by
  rw [raiseExponent, if_pos h]

/-- The exponent jump is less than one extra period above the binary length.
This controls the arithmetic size of the computable construction. -/
theorem raise_size_bound (a e S : Nat) :
    raiseExponent a e S ≤ e+bitLength S+periodLength a := by
  unfold raiseExponent
  split
  · omega
  · have hd := Nat.div_add_mod (bitLength S) (periodLength a)
    have hm : periodLength a*(bitLength S/periodLength a+1) =
        periodLength a*(bitLength S/periodLength a)+periodLength a := by
      rw [Nat.mul_add, Nat.mul_one]
    omega

end Collatz.Exploration.ExponentRaise
