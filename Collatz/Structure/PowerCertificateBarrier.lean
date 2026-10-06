import Collatz.Structure.PowerDensityParameters

/-!
# Exact exponent boundary of the homogeneous parity-moment certificate

The certificate method succeeds exactly when 3^q<4^p. This is a limitation of
these sufficient conditions, not an impossibility theorem for power-density
bounds proved by other methods.
-/
namespace Collatz.PowerCertificateBarrier
open ParityMoments PowerDensityParameters

/-- Integral arithmetic-geometric mean inequality for an ordered pair. -/
theorem four_mul_le_square {A B : Nat} (h : B≤A) : 4*(A*B)≤(A+B)^2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.add_mul, Nat.mul_add]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.reduceMul]
  simp only [← Nat.mul_assoc]
  omega

/-- Below half the odd-step count, squaring a homogeneous weight is no larger
than the product of complementary weights. -/
theorem low_weight_square {A B K h : Nat} (hAB : B≤A) (hh : 2*h≤K) :
    (weight A B K h)^2≤(A*B)^K := by
  have hle : h≤K-h := by omega
  have hm := weight_mono hAB hle (Nat.sub_le K h)
  have ht := Nat.mul_le_mul_left (weight A B K h) hm
  have he : K-(K-h)=h := by omega
  have hsum : h+(K-h)=K := by omega
  have hprod : weight A B K h*weight A B K (K-h)=(A*B)^K := by
    simp only [weight, he, Nat.mul_pow]
    calc
      A^h*B^(K-h)*(A^(K-h)*B^h) = (A^h*A^(K-h))*(B^h*B^(K-h)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = A^K*B^K := by rw [← Nat.pow_add, ← Nat.pow_add, hsum]
  rw [hprod] at ht
  simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using ht

/-- A tail threshold at or below half cannot beat the uniform moment average. -/
theorem no_moment_gap_at_half {A B K h : Nat} (hAB : B≤A) (hh : 2*h≤K) :
    2^K*weight A B K h≤(A+B)^K := by
  have hw := low_weight_square hAB hh
  have hm := Nat.mul_le_mul_left ((2^K)^2) hw
  have ha := Nat.pow_le_pow_left (four_mul_le_square hAB) K
  have hmid : (2^K)^2*(A*B)^K=(4*(A*B))^K := by
    have hp : (2^K)^2=(4:Nat)^K := by
      rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
    simp only [hp, Nat.mul_pow]
  rw [hmid] at hm
  have hfinal := Nat.le_trans hm ha
  have hn : (2^K*weight A B K h)^2≤((A+B)^K)^2 := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm] using hfinal
  exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp hn

/-- A certificate's strict moment gap requires strictly more than half odd steps. -/
theorem threshold_above_half {p q : Nat} (c : Certificate p q) : c.block<2*c.threshold := by
  by_cases hh : 2*c.threshold≤c.block
  · have hn := no_moment_gap_at_half c.weights_order hh
    have hg := c.moment_gap
    change 2^c.block*(c.oddWeight^c.threshold*c.evenWeight^(c.block-c.threshold))≤
      (c.oddWeight+c.evenWeight)^c.block at hn
    omega
  · omega

/-- The multiplier gap and above-half threshold force Korec's exponent condition. -/
theorem exponent_condition {p q : Nat} (c : Certificate p q) : 3^q<4^p := by
  by_cases hg : 3^q<4^p
  · exact hg
  · have hreverse : 4^p≤3^q := by omega
    have hbase := Nat.pow_le_pow_left hreverse c.block
    have he := Nat.mul_le_mul_left q (Nat.le_of_lt (threshold_above_half c))
    have hodd := Nat.pow_le_pow_right (by decide : 1≤(3:Nat)) he
    have hmult := Nat.pow_lt_pow_left c.multiplier_gap (by decide : 2≠0)
    have hlo : (4^p)^c.block≤(3^(q*c.threshold))^2 := by
      apply Nat.le_trans hbase
      simpa only [← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hodd
    have hhi : (3^(q*c.threshold))^2<(4^p)^c.block := by
      have hp : (4:Nat)=2^2 := rfl
      simpa only [hp, ← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using hmult
    omega

/-- Exact characterization of this certificate method's exponent range. -/
theorem certificate_iff_exponent_condition (p q : Nat) :
    Nonempty (Certificate p q) ↔ 3^q<4^p :=
  ⟨fun ⟨c⟩ => exponent_condition c, certificate_exists p q⟩

/-- The 3/4 exponent cannot be established with this certificate format.
This does not assert failure of the actual 3/4 power-density conclusion. -/
theorem no_three_quarters_certificate : ¬Nonempty (Certificate 3 4) := by
  rw [certificate_iff_exponent_condition]
  decide

end Collatz.PowerCertificateBarrier
