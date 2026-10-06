/-!
# Explicit integer precision for a strict geometric gap

If 0<a<b, then q*a^s<b^s as soon as q*a≤s. The cutoff is deliberately coarse:
it supplies a finite threshold without real limits, logarithms, or division.
-/
namespace Collatz.GeometricPrecision

/-- A homogeneous integer form of Bernoulli's inequality. -/
theorem linear_gain (a b s : Nat) (hab : a<b) : (a+s)*a^s≤a*b^s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hc : (a+s+1)*a≤(a+s)*b := by
      calc
        (a+s+1)*a ≤ (a+s)*(a+1) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
          omega
        _ ≤ (a+s)*b := Nat.mul_le_mul_left _ (by omega)
    have hm := Nat.mul_le_mul_right (a^s) hc
    have ht := Nat.mul_le_mul_right b ih
    have ht' : (a+s)*b*a^s≤a*b^(s+1) := by
      simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht
    have hfinal := Nat.le_trans hm ht'
    simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc] using hfinal

/-- Every prescribed integer factor is eventually absorbed by a strict
geometric gap. The conclusion holds at all later exponents, not just one. -/
theorem scaled_power_lt (a b q s : Nat) (ha : 0<a) (hab : a<b) (hs : q*a≤s) :
    q*a^s<b^s := by
  have hc : q*a<a+s := by omega
  have hm := Nat.mul_lt_mul_of_pos_right hc (Nat.pow_pos ha : 0<a^s)
  have ht := Nat.lt_of_lt_of_le hm (linear_gain a b s hab)
  have he : q*a*a^s=a*(q*a^s) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [he] at ht
  exact Nat.lt_of_mul_lt_mul_left ht

/-- An eventual form convenient for count estimates. -/
theorem eventually_scaled_power_lt (a b q : Nat) (ha : 0<a) (hab : a<b) :
    ∃ S, ∀ s, S≤s → q*a^s<b^s :=
  ⟨q*a, fun s hs => scaled_power_lt a b q s ha hab hs⟩

end Collatz.GeometricPrecision
