import Collatz.Exploration.ClassWitnessCost

/-!
# Size control for inverse-class witnesses

Successful-time control alone does not limit the magnitude of a constructed
input. Here a separate elementary estimate gives a linear bound in the affine
threshold for a fixed class. The multiplicative factor includes an exponential
of the ternary period, so it is deliberately a coarse upper bound.

An existential member in an interval does not prove a positive density of
convergent inputs. These estimates describe the particular construction and
keep that quantifier distinction explicit.
-/
namespace Collatz.Exploration.WitnessSize

open ComputedClassWitness ExponentRaise ExponentSearch

/-- Binary length overshoots its argument by at most a factor of two, with a
one-unit correction ensuring the same statement includes zero. -/
theorem binary_power_bound (S : Nat) : 2^(bitLength S) ≤ 2*(S+1) := by
  by_cases hz : S = 0
  · subst S; decide
  · have hp := Nat.log2_self_le hz
    unfold bitLength
    rw [Nat.pow_succ]
    omega

/-- The affine index never exceeds the matched power. -/
theorem matchingIndex_le_power {a B N e : Nat} (h : (2:Nat)^e%3^a = B%3^a) :
    matchingIndex a B N e ≤ 2^(raiseExponent a e (3^a*N+B)) := by
  have hs := (matchingIndex_spec (N := N) h).2
  have hp : 1 ≤ 3^a := Nat.pow_pos (by decide : 0 < (3:Nat))
  have hm := Nat.mul_le_mul_right (matchingIndex a B N e) hp
  simp only [Nat.one_mul] at hm
  omega

/-- A bound on the power produced after finite search and exponent raising. -/
theorem raised_value_bound {a B N e : Nat} (he : findUnitExponent a B = some e) :
    2^(raiseExponent a e (3^a*N+B)) ≤
      2^(2*periodLength a)*(2*(3^a*N+B+1)) := by
  have hx := chosen_exponent_bound (N := N) he
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (Nat.le_of_lt hx)
  have hb := binary_power_bound (3^a*N+B)
  have hm := Nat.mul_le_mul_left (2^(2*periodLength a)) hb
  rw [Nat.pow_add] at hp
  have hcomm : 2^(bitLength (3^a*N+B))*2^(2*periodLength a) =
      2^(2*periodLength a)*2^(bitLength (3^a*N+B)) := Nat.mul_comm _ _
  rw [hcomm] at hp
  exact Nat.le_trans hp hm

/-- The full constructed input is at most a linear expression in the threshold,
with an explicit constant depending on its dyadic class. -/
theorem constructed_size_bound {k r N e : Nat}
    (he : findUnitExponent (oddCount r k) (acceleratedOrbit k r) = some e) :
    2^k*matchingIndex (oddCount r k) (acceleratedOrbit k r) N e+r ≤
      2^k*(2^(2*periodLength (oddCount r k))*
        (2*(3^(oddCount r k)*N+acceleratedOrbit k r+1)))+r := by
  have hi := matchingIndex_le_power (N := N) (findUnitExponent_sound he).2
  have hp := raised_value_bound (N := N) he
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (2^k) (Nat.le_trans hi hp)) r

/-- The size bound attaches directly to the executable function's output. -/
theorem returned_size_bound {k r N n : Nat} (h : classWitness k r N = some n) :
    n ≤ 2^k*(2^(2*periodLength (oddCount r k))*
      (2*(3^(oddCount r k)*N+acceleratedOrbit k r+1)))+r := by
  unfold classWitness at h
  cases he : findUnitExponent (oddCount r k) (acceleratedOrbit k r) with
  | none => simp [he] at h
  | some e =>
    have hn : 2^k*matchingIndex (oddCount r k) (acceleratedOrbit k r) N e+r = n := by
      simpa [he] using h
    rw [← hn]
    exact constructed_size_bound he

end Collatz.Exploration.WitnessSize
