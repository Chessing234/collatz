import Collatz.Structure.StoppingRuleDensity
import Collatz.Structure.StoppingNaturalDensity

/-!
# Density transport through the first actual descent

The first descent time is totalized to zero on starts that never descend.
Its distribution is tight in natural density, by the proved uniform
finite-horizon stopping estimate. Consequently the first-descent map preserves
density one under preimage, without assuming a uniform stopping horizon.
-/
namespace Collatz.FirstDescentDensityTransport
open NaturalDensity StoppingRuleDensity FirstLightConsequences

/-- An actual descent has a first occurrence. No coefficient-crossing
certificate is required for this elementary least-time statement. -/
theorem first_descent_exists {n k : Nat} (hd : acceleratedOrbit k n<n) :
    ∃ j, j≤k ∧ FirstDescent n j := by
  classical
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hex : ∃ j, j<k ∧ acceleratedOrbit j n<n
    · obtain ⟨j, hj, hdrop⟩ := hex
      obtain ⟨i, hi, hf⟩ := ih j hj hdrop
      exact ⟨i, by omega, hf⟩
    · refine ⟨k, Nat.le_refl _, hd, ?_⟩
      intro j hj
      have hn : ¬acceleratedOrbit j n<n := fun h => hex ⟨j, hj, h⟩
      omega

/-- Existence in the original finite-stopping-time interface. -/
theorem first_exists {n : Nat} (h : hasFiniteStoppingTime n) : ∃ k, FirstDescent n k := by
  obtain ⟨k, _, hk⟩ := h
  obtain ⟨j, _, hj⟩ := first_descent_exists hk
  exact ⟨j, hj⟩

/-- First actual descent time; zero when the orbit never falls below its start.
The default is a totalization convention, not an assertion of descent. -/
noncomputable def firstTime (n : Nat) : Nat := by
  classical
  exact if h : hasFiniteStoppingTime n then Classical.choose (first_exists h) else 0

/-- On descending inputs, the selected time has the exact least-time meaning. -/
theorem firstTime_spec {n : Nat} (h : hasFiniteStoppingTime n) : FirstDescent n (firstTime n) := by
  classical
  unfold firstTime
  rw [dif_pos h]
  exact Classical.choose_spec (first_exists h)

/-- Every observed descent bounds the selected first time from above. -/
theorem firstTime_le_of_drop {n k : Nat} (hd : acceleratedOrbit k n<n) : firstTime n≤k := by
  have hf : hasFiniteStoppingTime n :=
    (StoppingNaturalDensity.eventuallyDrops_iff_hasFiniteStoppingTime n).mp ⟨k, hd⟩
  have hs := firstTime_spec hf
  by_cases hk : firstTime n≤k
  · exact hk
  · have := hs.2 k (by omega)
    omega

/-- A large first time forces survival of every earlier finite horizon. -/
theorem long_time_no_drop {n H : Nat} (h : H<firstTime n) :
    StoppingNaturalDensity.NoDropThrough H n := by
  intro k hk
  by_cases hd : acceleratedOrbit k n<n
  · have := firstTime_le_of_drop hd
    omega
  · omega

/-- The proved stopping distribution supplies the uniform tail condition. -/
theorem firstTime_density_tight : DensityTight firstTime := by
  intro q hq
  refine ⟨160*q, (2*q)*((160*q)*3^(160*q)+1+2^(160*q)), ?_⟩
  intro N hn
  have hc := predicateCount_mono (P := fun n => 160*q<firstTime n)
    (Q := StoppingNaturalDensity.NoDropThrough (160*q))
    (fun _ h => long_time_no_drop h) N
  exact Nat.le_trans (Nat.mul_le_mul_left q hc)
    (StoppingNaturalDensity.noDrop_precision q N hq hn)

/-- The first-descent map, with the start left unchanged on non-descending inputs. -/
noncomputable def descentMap (n : Nat) : Nat := acceleratedOrbit (firstTime n) n

/-- A justified unbounded-time transport theorem: the time tail is controlled. -/
theorem density_one_descentMap {P : Nat → Prop} (hP : DensityOne P) :
    DensityOne (fun n => P (descentMap n)) :=
  density_one_tight_rule hP firstTime firstTime_density_tight

/-- The induced map strictly decreases exactly when finite stopping holds. -/
theorem descentMap_lt_iff (n : Nat) : descentMap n<n ↔ hasFiniteStoppingTime n := by
  constructor
  · intro h
    exact (StoppingNaturalDensity.eventuallyDrops_iff_hasFiniteStoppingTime n).mp ⟨firstTime n, h⟩
  · intro h
    exact (firstTime_spec h).1

/-- A single accelerated step cannot reduce size by more than a factor two. -/
theorem input_le_twice_step (n : Nat) : n≤2*acceleratedStep n := by
  unfold acceleratedStep
  split <;> omega

/-- A first descent ends at or above half the starting value: the preceding
state had not yet fallen below the start. -/
theorem first_descent_half_bound {n k : Nat} (h : FirstDescent n k) :
    n≤2*acceleratedOrbit k n := by
  have hk : 0<k := by
    by_cases hz : k=0
    · subst k
      have := h.1
      simp only [acceleratedOrbit_zero] at this
      omega
    · omega
  have hprev := h.2 (k-1) (by omega)
  have hs := input_le_twice_step (acceleratedOrbit (k-1) n)
  rw [← acceleratedOrbit_succ_step] at hs
  have he : k-1+1=k := by omega
  rw [he] at hs
  omega

/-- The totalized induced map obeys the same lower size bound everywhere. -/
theorem descentMap_half_bound (n : Nat) : n≤2*descentMap n := by
  classical
  by_cases h : hasFiniteStoppingTime n
  · exact first_descent_half_bound (firstTime_spec h)
  · simp only [descentMap, firstTime, dif_neg h, acceleratedOrbit_zero]
    omega

/-- For n≥32, the first descent alone cannot achieve the strict 4/5 target.
Later iterates can still achieve it, as the density theorem establishes. -/
theorem not_four_fifths_at_first_descent {n : Nat} (hn : 32≤n) :
    n^4≤(descentMap n)^5 := by
  by_cases h : n^4≤(descentMap n)^5
  · exact h
  · have hp := Nat.pow_le_pow_left (descentMap_half_bound n) 5
    simp only [Nat.mul_pow, show (2:Nat)^5=32 from rfl] at hp
    have hm := Nat.mul_lt_mul_of_pos_left (by omega : (descentMap n)^5<n^4)
      (by decide : 0<32)
    have hcoeff := Nat.mul_le_mul_right (n^4) hn
    have hlast : 32*n^4≤n^5 := by
      simpa only [Nat.pow_succ, Nat.mul_comm] using hcoeff
    omega

end Collatz.FirstDescentDensityTransport
