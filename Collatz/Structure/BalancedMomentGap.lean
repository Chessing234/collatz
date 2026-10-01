import Collatz.Structure.GeometricPrecision

/-!
# Strict moment gaps arbitrarily close to balanced parity

The integer inequality r^(2r)<(r+1)^(r+1)(r-1)^(r-1), for r≥2,
supplies a strict moment gap for parity thresholds tending to one half.
The proof uses a finite difference estimate for powers, without real calculus.
-/
namespace Collatz.BalancedMomentGap

/-- A discrete upper bound for the difference of adjacent powers. -/
theorem successor_power_bound (a s : Nat) :
    (a+1)^(s+1)≤a^(s+1)+(s+1)*(a+1)^s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hm := Nat.mul_le_mul_right a ih
    have hc := Nat.mul_le_mul_left ((s+1)*(a+1)^s) (Nat.le_succ a)
    have hc' : (s+1)*(a+1)^s*a≤(s+1)*(a+1)^(s+1) := by
      simpa only [Nat.pow_succ, Nat.mul_assoc] using hc
    calc
      (a+1)^(s+1+1) = (a+1)^(s+1)*a+(a+1)^(s+1) := by
        rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one]
      _ ≤ (a^(s+1)+(s+1)*(a+1)^s)*a+(a+1)^(s+1) :=
        Nat.add_le_add_right hm _
      _ ≤ a^(s+1)*a+(s+1)*(a+1)^(s+1)+(a+1)^(s+1) := by
        rw [Nat.add_mul]
        exact Nat.add_le_add_right (Nat.add_le_add_left hc' _) _
      _ = a^(s+1+1)+(s+1+1)*(a+1)^(s+1) := by
        simp only [Nat.pow_succ, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

/-- The polynomial coefficient that makes the balanced perturbation strict. -/
theorem coefficient_gap (t : Nat) :
    ((t+2)^2)^2+(t+3)^2*(t+1)<(t+3)^2*(t+2)^2 := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul]
  simp only [Nat.add_mul, Nat.mul_add]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_one,
    Nat.one_mul, Nat.reduceMul, Nat.reduceAdd]
  simp only [← Nat.mul_assoc]
  omega

/-- Moving one unit from an equal pair strictly increases this homogeneous
power product. The shift t+2 avoids truncated subtraction at small inputs. -/
theorem balanced_power_gap (t : Nat) :
    (t+2)^(2*(t+2)) < (t+3)^(t+3)*(t+1)^(t+1) := by
  let a := (t+3)*(t+1)
  let b := (t+2)^2
  have he : a+1=b := by
    dsimp [a, b]
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  have hbase := successor_power_bound a t
  rw [he] at hbase
  have hm := Nat.mul_le_mul_left ((t+3)^2) hbase
  have hcbase : b^2+(t+3)^2*(t+1)<(t+3)^2*b := coefficient_gap t
  have hc := Nat.mul_lt_mul_of_pos_right hcbase
    (Nat.pow_pos (Nat.pow_pos (by omega : 0<t+2)) : 0<b^t)
  have hleft : b^(t+2)+(t+3)^2*((t+1)*b^t)<(t+3)^2*b^(t+1) := by
    rw [Nat.pow_succ b (t+1), Nat.pow_succ b t]
    have hb2 : b^2=b*b := by simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    rw [hb2] at hc
    simpa only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hc
  rw [Nat.mul_add] at hm
  have hg : b^(t+2)<(t+3)^2*a^(t+1) := by omega
  have hl : b^(t+2)=(t+2)^(2*(t+2)) := by
    dsimp [b]
    rw [← Nat.pow_mul]
  have hr : (t+3)^2*a^(t+1)=(t+3)^(t+3)*(t+1)^(t+1) := by
    dsimp [a]
    rw [Nat.mul_pow, ← Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  rw [hl, hr] at hg
  exact hg

/-- A strict two-parameter moment gap at any of these near-balanced ratios. -/
theorem moment_gap (t : Nat) :
    (2*(t+2))^(2*(t+2)) <
      2^(2*(t+2))*((t+3)^(t+3)*(t+1)^(t+1)) := by
  rw [Nat.mul_pow]
  exact Nat.mul_lt_mul_of_pos_left (balanced_power_gap t) (Nat.pow_pos (by decide))

end Collatz.BalancedMomentGap
