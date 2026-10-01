import Collatz.Structure.BalancedMomentGap
import Collatz.Structure.ParityMoments

/-! Integer certificates for a rational power-density argument and their
construction throughout Korec's recorded rational-exponent range. -/
namespace Collatz.PowerDensityParameters

/-- A finite collection of strict integer gaps sufficient for the counting
and affine parts of a power-density proof. No density assertion is a field. -/
structure Certificate (p q : Nat) where
  block : Nat
  threshold : Nat
  oddWeight : Nat
  evenWeight : Nat
  block_pos : 0<block
  threshold_le : threshold≤block
  weights_order : evenWeight≤oddWeight
  weights_pos : 0<oddWeight+evenWeight
  moment_gap : (oddWeight+evenWeight)^block <
    2^block*(oddWeight^threshold*evenWeight^(block-threshold))
  multiplier_gap : 3^(q*threshold)<2^(p*block)

/-- The published strict threshold leaves room for a parity threshold
strictly above one half, at an explicit finite block length. -/
theorem multiplier_gap_exists (p q : Nat) (h : 3^q<4^p) :
    ∃ t, 3^(q*(t+3))<2^(p*(2*(t+2))) := by
  let a := 3^q
  let t := a*a
  have hg := GeometricPrecision.scaled_power_lt a (4^p) a (t+2)
    (Nat.pow_pos (by decide)) h (by dsimp [t]; omega)
  have hl : a*a^(t+2)=3^(q*(t+3)) := by
    dsimp [a]
    rw [Nat.mul_comm, ← Nat.pow_succ, ← Nat.pow_mul]
  have hr : (4^p)^(t+2)=2^(p*(2*(t+2))) := by
    rw [show (4:Nat)=2^2 from rfl, ← Nat.pow_mul, ← Nat.pow_mul]
    congr 1
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact ⟨t, by simpa only [hl, hr] using hg⟩

/-- Every admissible rational exponent has a certificate consisting solely
of natural numbers and verified inequalities. -/
theorem certificate_exists (p q : Nat) (h : 3^q<4^p) : Nonempty (Certificate p q) := by
  obtain ⟨t, ht⟩ := multiplier_gap_exists p q h
  refine ⟨{
    block := 2*(t+2)
    threshold := t+3
    oddWeight := t+3
    evenWeight := t+1
    block_pos := by omega
    threshold_le := by omega
    weights_order := by omega
    weights_pos := by omega
    moment_gap := ?_
    multiplier_gap := ht
  }⟩
  have he : 2*(t+2)-(t+3)=t+1 := by omega
  have hsum : (t+3)+(t+1)=2*(t+2) := by omega
  rw [he, hsum]
  exact BalancedMomentGap.moment_gap t

end Collatz.PowerDensityParameters
