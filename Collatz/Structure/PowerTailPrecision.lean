import Collatz.Structure.ParityMoments
import Collatz.Structure.GeometricPrecision

/-! The 125-step parity tail tends to zero with explicit integer precision.
This is the residue-count component of a prospective 4/5 power-density proof. -/
namespace Collatz.PowerTailPrecision
open ParityMoments

/-- Every requested reciprocal precision holds at all sufficiently large
block counts. The very coarse cutoff is explicit. -/
theorem tail_precision (q s : Nat) (hs : q*125^125≤s) :
    q*tailCount (125*s) (63*s)<2^(125*s) := by
  have hgap := GeometricPrecision.scaled_power_lt (125^125)
    (2^125*(63^63*62^62)) q s
    (Nat.pow_pos (by decide)) four_fifths_moment_gap hs
  have hcount := Nat.mul_le_mul_left q (four_fifths_tail_bound s)
  have ht := Nat.lt_of_le_of_lt hcount hgap
  have hnorm : (63^63*62^62)^s*(q*tailCount (125*s) (63*s)) <
      (63^63*62^62)^s*2^(125*s) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using ht
  exact Nat.lt_of_mul_lt_mul_left hnorm

/-- The concentration estimate in an eventual form, with no density or
orbit-threshold assertion hidden in its statement. -/
theorem eventually_tail_precision (q : Nat) : ∃ S, ∀ s, S≤s →
    q*tailCount (125*s) (63*s)<2^(125*s) :=
  ⟨q*125^125, fun s hs => tail_precision q s hs⟩

end Collatz.PowerTailPrecision
