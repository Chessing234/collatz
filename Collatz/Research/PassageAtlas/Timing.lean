import Collatz.Research.PassageAtlas.Horizon
import Collatz.Research.StoppingAtlas.Timing

/-! A deterministic constraint on first-passage times. No random parity
model is imposed on individual trajectories. -/
namespace Collatz.Research.PassageAtlas
open FirstLightDescent

/-- A dyadic half-open band contains at most one power of three. -/
theorem power_band_unique {k a b : Nat}
    (ha : 2 ^ k ≤ 3 ^ a ∧ 3 ^ a < 2 ^ (k + 1))
    (hb : 2 ^ k ≤ 3 ^ b ∧ 3 ^ b < 2 ^ (k + 1)) : a = b := by
  have hnot : ∀ x y : Nat,
      2 ^ k ≤ 3 ^ x → 3 ^ y < 2 ^ (k + 1) → ¬ x < y := by
    intro x y hx hy hxy
    have hp : (3 : Nat) ^ (x + 1) ≤ 3 ^ y :=
      Nat.pow_le_pow_right (by decide) hxy
    have hm := Nat.mul_le_mul_left 3 hx
    have hpos := Nat.two_pow_pos k
    rw [Arith.three_pow_succ] at hp
    rw [Arith.two_pow_succ] at hy
    omega
  have hab := hnot a b ha.1 hb.2
  have hba := hnot b a hb.1 ha.2
  omega

/-- All trajectories first crossing at the same time have the same odd-step count. -/
theorem firstLight_oddCount_unique {n m k : Nat}
    (hn : FirstLight n (k + 1)) (hm : FirstLight m (k + 1)) :
    oddCount n (k + 1) = oddCount m (k + 1) :=
  power_band_unique (StoppingAtlas.firstLight_power_band hn)
    (StoppingAtlas.firstLight_power_band hm)

/-- First crossings with a common odd count occur at a common time. -/
theorem firstLight_time_unique_of_count {n m j k : Nat}
    (hn : FirstLight n (j + 1)) (hm : FirstLight m (k + 1))
    (hc : oddCount n (j + 1) = oddCount m (k + 1)) : j = k := by
  have hj := StoppingAtlas.firstLight_power_band hn
  have hk := StoppingAtlas.firstLight_power_band hm
  rw [hc] at hj
  have hnot : ∀ x y : Nat,
      3 ^ oddCount m (k + 1) < 2 ^ (x + 1) →
      2 ^ y ≤ 3 ^ oddCount m (k + 1) → ¬ x < y := by
    intro x y hx hy hxy
    have hp : (2 : Nat) ^ (x + 1) ≤ 2 ^ y :=
      Nat.pow_le_pow_right (by decide) hxy
    omega
  have h1 := hnot j k hj.2 hk.1
  have h2 := hnot k j hk.2 hj.1
  omega

/-- The empty power band forbids coefficient first-passage at fourteen globally. -/
theorem no_firstLight_fourteen (n : Nat) : ¬ FirstLight n 14 :=
  StoppingAtlas.no_firstLight_of_empty_band 13 (by decide) n

/-- Transfer the global coefficient exclusion to actual exact stopping. -/
theorem no_stopping_fourteen (n : Nat) : ¬ stoppingTime n 14 := by
  intro hs
  have hn := CoefficientDescent.start_gt_one hs
  exact no_firstLight_fourteen n ((stopping_iff_firstLight_le_2592 hn (by decide)).mp hs)

/-- Exact stopping times in the certified range determine a single odd count. -/
theorem stopping_oddCount_unique {n m k : Nat} (hk : k + 1 ≤ 2592)
    (hn : stoppingTime n (k + 1)) (hm : stoppingTime m (k + 1)) :
    oddCount n (k + 1) = oddCount m (k + 1) := by
  exact firstLight_oddCount_unique
    ((stopping_iff_firstLight_le_2592 (CoefficientDescent.start_gt_one hn) hk).mp hn)
    ((stopping_iff_firstLight_le_2592 (CoefficientDescent.start_gt_one hm) hk).mp hm)

end Collatz.Research.PassageAtlas
