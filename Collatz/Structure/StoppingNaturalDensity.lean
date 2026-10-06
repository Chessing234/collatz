import Collatz.Strategy.FirstLightEventual
import Collatz.Structure.DensityPrecision

/-!
# Natural density one of finite stopping time

The actual-orbit density conclusion follows from the repository's geometric
heavy-residue estimate and an explicit exceptional-start interval. This is a
formal reconstruction of the classical Terras/Everett stopping-time result,
not a proof of convergence to 1 and not a claim of historical novelty.
-/
namespace Collatz.StoppingNaturalDensity
open NaturalDensity PeriodicCounting FirstLightCounting FirstLightEventual

/-- No actual descent during a fixed finite window, without shifting the input. -/
def NoDropThrough (H n : Nat) : Prop := ∀ j, j≤H → n≤acceleratedOrbit j n

/-- The eventual-descent predicate at the original starting integer. -/
def EventuallyDrops (n : Nat) : Prop := ∃ k, acceleratedOrbit k n<n

/-- Actual non-descent counts are controlled by complete periods plus a finite error. -/
theorem noDrop_count_bound (H N : Nat) :
    predicateCount (NoDropThrough H) N ≤
      (H*3^H+1)+(N/2^H+1)*Density.heavyCount H := by
  have he := predicateCount_eventual_mono (P := NoDropThrough H)
    (Q := fun n => heavyCheck H n=true) (H*3^H+1) N (by
      intro n hn hnd
      exact (no_descent_iff_heavy_above_threshold (by omega)).mp hnd)
  rw [predicateCount_bool] at he
  have hb := (periodic_count_bounds (heavyCheck H) (2^H) N
    (Nat.pow_pos (by decide)) (heavyCheck_period H)).2
  have hc : countBelow (heavyCheck H) (2^H)≤Density.heavyCount H := by
    rw [← survival_period_count]
    exact survival_count_le_heavy H
  exact Nat.le_trans he (Nat.add_le_add_left
    (Nat.le_trans hb (Nat.mul_le_mul_left _ hc)) _)

/-- Every input outside the finite-window non-descent set eventually drops. -/
theorem eventuallyDrops_of_not_noDrop {H n : Nat} (h : ¬ NoDropThrough H n) :
    EventuallyDrops n := by
  classical
  by_cases hex : EventuallyDrops n
  · exact hex
  · apply False.elim
    apply h
    intro j _
    by_cases hd : acceleratedOrbit j n<n
    · exact False.elim (hex ⟨j, hd⟩)
    · omega

/-- The non-descent count has arbitrary precision at an explicit large cutoff. -/
theorem noDrop_precision (q N : Nat) (hq : 0<q)
    (hN : (2*q)*((160*q)*3^(160*q)+1+2^(160*q))≤N) :
    q*predicateCount (NoDropThrough (160*q)) N ≤ N := by
  let H := 160*q
  let B := H*3^H+1
  let M := 2^H
  let A := Density.heavyCount H
  let C := predicateCount (NoDropThrough H) N
  have hb : C≤B+(N/M+1)*A := noDrop_count_bound H N
  have ha : (2*q)*A≤M := by
    have h := DensityPrecision.heavy_precision (2*q)
    have he : 80*(2*q)=H := by simp only [H]; omega
    simpa only [he] using h
  have hAM : A≤M := by
    have hlo : A≤(2*q)*A := by
      have ht := Nat.mul_le_mul_right A (show 1≤2*q by omega)
      simpa only [Nat.one_mul] using ht
    exact Nat.le_trans hlo ha
  have hextra : (2*q)*(B+A)≤N :=
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hAM B)) hN
  have hperiod : (N/M)*((2*q)*A)≤N :=
    Nat.le_trans (Nat.mul_le_mul_left (N/M) ha) (Nat.div_mul_le_self N M)
  have htotal := Nat.mul_le_mul_left (2*q) hb
  have he : (2*q)*(B+(N/M+1)*A) =
      (2*q)*(B+A)+(N/M)*((2*q)*A) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul]
    ac_rfl
  rw [he] at htotal
  have htwo : (2*q)*C≤N+N := Nat.le_trans htotal (Nat.add_le_add hextra hperiod)
  simp only [Nat.mul_assoc] at htwo
  change q*C≤N
  omega

/-- Almost every starting integer has finite stopping time, in natural density. -/
theorem eventuallyDrops_density_one : DensityOne EventuallyDrops := by
  intro q hq
  refine ⟨(2*q)*((160*q)*3^(160*q)+1+2^(160*q)), ?_⟩
  intro N hn
  have hbad := noDrop_precision q N hq hn
  have hparts := predicateCount_complement (NoDropThrough (160*q)) N
  have hgood := predicateCount_mono
    (P := fun n => ¬ NoDropThrough (160*q) n) (Q := EventuallyDrops)
    (fun _ h => eventuallyDrops_of_not_noDrop h) N
  have hsum : N≤predicateCount (NoDropThrough (160*q)) N+
      predicateCount EventuallyDrops N := by omega
  have hscaled := Nat.mul_le_mul_left q hsum
  rw [Nat.mul_add] at hscaled
  have he : q*N=(q-1)*N+N := by
    have hq' : q=q-1+1 := by omega
    calc q*N = (q-1+1)*N := congrArg (fun x => x*N) hq'
         _ = (q-1)*N+N := by rw [Nat.add_mul, Nat.one_mul]
  omega

/-- The auxiliary descent predicate agrees with the existing positive-index definition. -/
theorem eventuallyDrops_iff_hasFiniteStoppingTime (n : Nat) :
    EventuallyDrops n ↔ hasFiniteStoppingTime n := by
  constructor
  · rintro ⟨k, hk⟩
    have hkpos : 1≤k := by
      cases k with
      | zero => simp only [acceleratedOrbit_zero] at hk; omega
      | succ k => omega
    exact ⟨k, hkpos, hk⟩
  · rintro ⟨k, _, hk⟩
    exact ⟨k, hk⟩

/-- Natural-density-one finite stopping time for the repository's original predicate. -/
theorem finite_stopping_time_density_one : DensityOne hasFiniteStoppingTime :=
  densityOne_mono (fun n h => (eventuallyDrops_iff_hasFiniteStoppingTime n).mp h)
    eventuallyDrops_density_one

end Collatz.StoppingNaturalDensity
