import Collatz.Strategy.FirstLightCounting
import Collatz.Core.Sum

/-! Exact transfer of finite counting mass between survival and first passage.
All identities are finite and unconditional for coefficients. An ExactThrough
certificate supplies the interpretation as actual first descent. -/
namespace Collatz.Research.StoppingAtlas
open FirstLightDescent FirstLightCounting FirstLightConsequences PeriodicCounting

/-- Shift by two to exclude the two inputs where actual first descent is exceptional. -/
def firstEventB (k n : Nat) : Bool := decide (FirstLight (n + 2) k)

/-- Under a crossing certificate this Boolean is precisely actual first descent. -/
theorem firstEvent_spec {H k n : Nat} (hH : ExactThrough H) (hk : k ≤ H) :
    firstEventB k n = true ↔ FirstDescent (n + 2) k := by
  rw [firstEventB, decide_eq_true_eq]
  exact (first_descent_iff_first_light hH (by omega) hk).symm

/-- Exact first events at different times are mutually exclusive. -/
theorem firstEvent_disjoint {j k n : Nat} (hne : j ≠ k)
    (hj : firstEventB j n = true) : firstEventB k n ≠ true := by
  intro hk
  have hjf := of_decide_eq_true hj
  have hkf := of_decide_eq_true hk
  exact hne (first_light_unique hjf hkf)

/-- Every exact-time event is periodic with its own binary modulus. -/
theorem firstEvent_period (k n : Nat) : firstEventB k (n + 2 ^ k) = firstEventB k n := by
  apply Bool.eq_iff_iff.mpr
  simp only [firstEventB, decide_eq_true_eq]
  apply FirstLightPeriodicity.firstLight_congr (H := k) (Nat.le_refl k)
  have he : n + 2 ^ k + 2 = n + 2 + 2 ^ k := by omega
  rw [he]
  simp

/-- Exact event counts on [2,N+2) split into full periods and a prefix. -/
theorem firstEvent_count_div_mod (k N : Nat) :
    countBelow (firstEventB k) N =
      (N / 2 ^ k) * countBelow (firstEventB k) (2 ^ k) +
        countBelow (firstEventB k) (N % 2 ^ k) :=
  count_div_mod _ _ _ (firstEvent_period k)

/-- A surviving coefficient prefix either survives one more step or first crosses there. -/
theorem heavy_split (H n : Nat) : heavyCheck H n = true ↔
    heavyCheck (H + 1) n = true ∨ FirstLight n (H + 1) := by
  rw [heavyCheck_iff, heavyCheck_iff]
  constructor
  · intro h
    by_cases he : 2 ^ (H + 1) ≤ 3 ^ oddCount n (H + 1)
    · left
      intro j hj
      by_cases hjH : j ≤ H
      · exact h j hjH
      · have : j = H + 1 := by omega
        simpa only [this] using he
    · right
      exact ⟨by omega, fun j hj => h j (by omega)⟩
  · intro h j hj
    rcases h with h | h
    · exact h j (by omega)
    · exact h.2 j (by omega)

/-- The two destinations of the survival split cannot overlap. -/
theorem heavy_split_disjoint (H n : Nat) :
    ¬ (heavyCheck (H + 1) n = true ∧ FirstLight n (H + 1)) := by
  rintro ⟨h, hf⟩
  have hb := (heavyCheck_iff _ _).mp h (H + 1) (Nat.le_refl _)
  have := hf.1
  omega

/-- Turn the disjoint logical split into a per-input counting identity. -/
theorem indicator_partition (H n : Nat) :
    (if survives H n then 1 else 0) =
      (if survives (H + 1) n then 1 else 0) + (if firstEventB (H + 1) n then 1 else 0) := by
  have hs : survives H n = true ↔ survives (H + 1) n = true ∨ firstEventB (H + 1) n = true := by
    simpa only [survives, firstEventB, decide_eq_true_eq] using heavy_split H (n + 2)
  have hd : ¬ (survives (H + 1) n = true ∧ firstEventB (H + 1) n = true) := by
    simpa only [survives, firstEventB, decide_eq_true_eq] using heavy_split_disjoint H (n + 2)
  cases ho : survives H n <;> cases hn : survives (H + 1) n <;>
    cases he : firstEventB (H + 1) n <;> simp_all

/-- Exact mass conservation at every finite cutoff, not only complete periods. -/
theorem count_partition (H N : Nat) :
    countBelow (survives H) N =
      countBelow (survives (H + 1)) N + countBelow (firstEventB (H + 1)) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [count_succ, count_succ, count_succ, ih]
    have := indicator_partition H N
    omega

/-- Total first-event mass accumulated through a finite horizon. -/
def stoppedCount (H N : Nat) : Nat :=
  Sum.sumRange H (fun j => countBelow (firstEventB (j + 1)) N)

/-- Before any steps every shifted positive input survives. -/
theorem survival_zero (N : Nat) : countBelow (survives 0) N = N := by
  have he : survives 0 = fun _ => true := by
    funext n
    simp [survives, heavyCheck, oddCount, parityVector]
  rw [he]
  exact count_full N

/-- A complete finite partition of all inputs into first events and remaining survivors. -/
theorem cumulative_conservation (H N : Nat) :
    stoppedCount H N + countBelow (survives H) N = N := by
  induction H with
  | zero => simp [stoppedCount, survival_zero]
  | succ H ih =>
    have hpart := count_partition H N
    change (Sum.sumRange H (fun j => countBelow (firstEventB (j + 1)) N) +
      countBelow (firstEventB (H + 1)) N) + countBelow (survives (H + 1)) N = N
    change Sum.sumRange H (fun j => countBelow (firstEventB (j + 1)) N) +
      countBelow (survives H) N = N at ih
    omega

/-- Every horizon extension transfers mass out of the survivor set, never into it. -/
theorem survival_count_antitone (H N : Nat) :
    countBelow (survives (H + 1)) N ≤ countBelow (survives H) N := by
  have := count_partition H N
  omega

end Collatz.Research.StoppingAtlas
