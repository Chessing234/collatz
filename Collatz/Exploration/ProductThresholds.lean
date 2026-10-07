import Collatz.Exploration.FloorProductDescent

/-! Coefficient-specific floor thresholds. Monotonicity certifies all larger floors,
not universal eventual descent or a novel analytic method. -/
namespace Collatz.Exploration.ProductThresholds
open FloorAffineError FloorProductError

def Passes (C D k b : Nat) : Prop := C*weight b^k < D*base b^k
instance (C D k b : Nat) : Decidable (Passes C D k b) :=
  inferInstanceAs (Decidable (_ < _))

theorem oddCeil_mono {b m : Nat} (h : b ≤ m) : oddCeil b ≤ oddCeil m := by
  unfold oddCeil
  split <;> split <;> omega

/-- Cleared-denominator monotonicity of the single floor factor. -/
theorem factor_mono {b m : Nat} (h : b ≤ m) : base b*weight m ≤ base m*weight b := by
  have hm := Nat.mul_le_mul_left 3 (oddCeil_mono h)
  change base b ≤ base m at hm
  have hw : ∀ x, weight x = base x+1 := fun x => rfl
  rw [hw,hw]
  simp only [Nat.mul_add,Nat.mul_one]
  have he : base b*base m = base m*base b := Nat.mul_comm _ _
  omega

/-- One exact threshold certificate proves the same coefficient test at every larger floor. -/
theorem passes_mono {C D k b m : Nat} (h : b ≤ m) (hp : Passes C D k b) :
    Passes C D k m := by
  have hpow := Nat.pow_le_pow_left (factor_mono h) k
  rw [Nat.mul_pow,Nat.mul_pow] at hpow
  have hw : 0 < weight m^k := Nat.pow_pos (by unfold weight; omega)
  have h1 := Nat.mul_lt_mul_of_pos_right hp hw
  have h2 := Nat.mul_le_mul_left D hpow
  simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] at h1 h2
  have hc : (C*weight m^k)*weight b^k < (D*base m^k)*weight b^k := by
    simp only [Nat.mul_left_comm,Nat.mul_comm]
    omega
  exact Nat.lt_of_mul_lt_mul_right hc

/-- Two neighboring evaluations classify all natural floors for a fixed coefficient pair. -/
theorem threshold_iff {C D k t : Nat} (ht : 0 < t)
    (hy : Passes C D k t) (hn : ¬ Passes C D k (t-1)) (b : Nat) :
    Passes C D k b ↔ t ≤ b := by
  constructor
  · intro hb
    by_cases h : t ≤ b
    · exact h
    · have hl : b ≤ t-1 := by omega
      exact False.elim (hn (passes_mono hl hb))
  · intro h
    exact passes_mono h hy

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem threshold65 (b : Nat) : Passes (3^41) (2^65) 41 b ↔ 1192 ≤ b := by
  apply threshold_iff (t := 1192) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem threshold59 (b : Nat) : Passes (3^37) (2^59) 37 b ↔ 50 ≤ b := by
  apply threshold_iff (t := 50) (by decide) (by decide) (by decide)

/-- The threshold certifies actual descent for every matching 65-step odd-count class. -/
theorem descent65 {n : Nat} (hn : 1192 ≤ n) (hc : oddCount n 65 = 41) :
    ∃ i, i ≤ 65 ∧ acceleratedOrbit i n < n := by
  have hp := (threshold65 n).mpr hn
  apply FloorProductDescent.descent_before (by omega)
  rw [hc]
  exact hp

/-- The corresponding 59-step class has a much smaller source threshold. -/
theorem descent59 {n : Nat} (hn : 50 ≤ n) (hc : oddCount n 59 = 37) :
    ∃ i, i ≤ 59 ∧ acceleratedOrbit i n < n := by
  have hp := (threshold59 n).mpr hn
  apply FloorProductDescent.descent_before (by omega)
  rw [hc]
  exact hp

end Collatz.Exploration.ProductThresholds
