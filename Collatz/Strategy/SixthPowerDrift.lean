import Collatz.Strategy.SortStair

/-!
An explicit sixth-power envelope for the existing staircase product bound.
This is a necessary condition for an injective never-dropping orbit, not
an exclusion of such orbits. The elementary estimate is not claimed novel.
-/
namespace Collatz.SixthPowerDrift
open StairBound

theorem single_factor (t : Nat) :
    (3 * (t+1) + 1)^6 * t ≤ (3*(t+1))^6 * (t+2) := by
  simp only [Nat.pow_succ, Nat.pow_zero]
  grind

/-- An exact integer version of a logarithmic bound on the +1 correction. -/
theorem staircase_envelope (t a : Nat) :
    stairPlus (t+1) a ^ 6 * t ≤
      (3^a * stair (t+1) a)^6 * (t+2*a) := by
  induction a with
  | zero => simp [stairPlus, stair]
  | succ a ih =>
    have hs := single_factor (t+2*a)
    have he : t + 1 + 2*a = (t+2*a)+1 := by omega
    calc
      stairPlus (t+1) (a+1)^6 * t
          = (3*(t+1+2*a)+1)^6 * (stairPlus (t+1) a^6*t) := by
            simp only [stairPlus, Nat.mul_pow, Nat.mul_assoc]
      _ ≤ (3*(t+1+2*a)+1)^6 * ((3^a*stair (t+1) a)^6*(t+2*a)) :=
            Nat.mul_le_mul_left _ ih
      _ = ((3*(t+2*a+1)+1)^6*(t+2*a)) * (3^a*stair (t+1) a)^6 := by
            rw [he]
            ac_rfl
      _ ≤ ((3*(t+2*a+1))^6*(t+2*a+2)) * (3^a*stair (t+1) a)^6 :=
            Nat.mul_le_mul_right _ hs
      _ = (3^(a+1)*stair (t+1) (a+1))^6*(t+2*(a+1)) := by
            rw [stair, Nat.pow_succ 3 a, he]
            have ht : t+2*(a+1) = t+2*a+2 := by omega
            rw [ht]
            simp only [Nat.mul_pow]
            ac_rfl

/-- Eliminate the large staircase products from the necessary condition. -/
theorem bound_of_staircase {t a k : Nat}
    (h : 2^k * stair (t+1) a ≤ stairPlus (t+1) a) :
    (2^k)^6*t ≤ (3^a)^6*(t+2*a) := by
  have hp := Nat.mul_le_mul_right t (Nat.pow_le_pow_left h 6)
  have he := staircase_envelope t a
  have hc := Nat.le_trans hp he
  simp only [Nat.mul_pow] at hc
  have hc' : ((2^k)^6*t) * stair (t+1) a^6 ≤
      ((3^a)^6*(t+2*a)) * stair (t+1) a^6 := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hc
  exact Nat.le_of_mul_le_mul_right hc' (Nat.pow_pos (stair_pos (by omega) a))

/-- A never-dropping orbit with distinct values satisfies this at every prefix. -/
theorem never_drop_bound {t k : Nat} (hodd : (t+1)%2=1)
    (hnd : ∀ i, t+1 ≤ acceleratedOrbit i (t+1))
    (hinj : ∀ i j, i<k → j<k →
      acceleratedOrbit i (t+1)=acceleratedOrbit j (t+1) → i=j) :
    (2^k)^6*t ≤ (3^(oddCount (t+1) k))^6*(t+2*oddCount (t+1) k) :=
  bound_of_staircase (SortStair.neverDrops_staircase (by omega) hodd hnd hinj)

/-- The direction matters: sufficiently many odd steps make the envelope
vacuous. This implication says nothing about realizing such counts by an orbit. -/
theorem envelope_allows_heavy {t a k : Nat} (h : 2^k ≤ 3^a) :
    (2^k)^6*t ≤ (3^a)^6*(t+2*a) := by
  exact Nat.le_trans (Nat.mul_le_mul_right t (Nat.pow_le_pow_left h 6))
    (Nat.mul_le_mul_left _ (by omega))

/-- A strict violation supplies actual descent; proving that every starting
value eventually supplies such a prefix remains an unproved obligation. -/
theorem descent_of_gap {t k : Nat} (hodd : (t+1)%2=1)
    (hinj : ∀ i j, i<k → j<k →
      acceleratedOrbit i (t+1)=acceleratedOrbit j (t+1) → i=j)
    (hgap : (3^(oddCount (t+1) k))^6*(t+2*oddCount (t+1) k) <
      (2^k)^6*t) :
    ∃ j, acceleratedOrbit j (t+1) < t+1 := by
  classical
  by_cases hd : ∃ j, acceleratedOrbit j (t+1) < t+1
  · exact hd
  · have hnd : ∀ i, t+1 ≤ acceleratedOrbit i (t+1) := by
      intro i
      have hn : ¬ acceleratedOrbit i (t+1) < t+1 :=
        fun hi => hd ⟨i, hi⟩
      omega
    have hb := never_drop_bound hodd hnd hinj
    omega

end Collatz.SixthPowerDrift
