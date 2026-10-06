import Collatz.Research.CoefficientDescent.Horizon
import Collatz.Research.CoefficientDescent.Transfer

/-! Resolve the earlier finite-interval census question through depth 256,
for all class representatives and all natural class indices. -/
namespace Collatz.Research.CoefficientDescent

open FirstLightDescent DescentIntervals

/-- Increasing the class index preserves exact first descent through the checked horizon. -/
theorem stopping_upward_le_256 {k r m u : Nat} (hk : k ≤ 256) (hmu : m ≤ u)
    (hs : stoppingTime (2 ^ k * m + r) k) : stoppingTime (2 ^ k * u + r) k := by
  have hn := start_gt_one hs
  have hf := (stopping_iff_firstLight_le_256 hn hk).mp hs
  have hr := (firstLight_class k r m).mp hf
  have hmul := Nat.mul_le_mul_left (2 ^ k) hmu
  have hnu : 1 < 2 ^ k * u + r := by omega
  exact (stopping_iff_firstLight_le_256 hnu hk).mpr ((firstLight_class k r u).mpr hr)

/-- Interval membership is upward closed at every depth up to 256. -/
theorem membership_upward_le_256 {k r m u : Nat} (hk : k ≤ 256) (hmu : m ≤ u)
    (hs : (exactInterval k r).Contains m) : (exactInterval k r).Contains u := by
  rw [exactInterval_spec] at hs ⊢
  exact stopping_upward_le_256 hk hmu hs

/-- Any bounded nonempty exact-time interval would have depth greater than 256. -/
theorem finite_nonempty_after_256 {k r : Nat}
    (hb : ∃ B, ∀ m, (exactInterval k r).Contains m → m < B)
    (hne : ∃ m, (exactInterval k r).Contains m) : 256 < k := by
  obtain ⟨n, _, hs, hf⟩ := finite_interval_witness hb hne
  exact delayed_stopping_after_256 hs hf

/-- A nonempty interval through depth 256 has no finite upper endpoint. -/
theorem upper_none_of_nonempty_le_256 {k r : Nat} (hk : k ≤ 256)
    (hne : ∃ m, (exactInterval k r).Contains m) : (exactInterval k r).upper = none := by
  cases hu : (exactInterval k r).upper with
  | none => rfl
  | some B =>
    have hb : ∃ B, ∀ m, (exactInterval k r).Contains m → m < B := by
      refine ⟨B, ?_⟩
      intro m hm
      have h := hm.2
      simpa only [hu] using h
    have := finite_nonempty_after_256 hb hne
    omega

/-- Complete shape dichotomy: empty or an infinite tail, for arbitrary representatives. -/
theorem empty_or_tail_le_256 (k r : Nat) (hk : k ≤ 256) :
    (∀ m, ¬ (exactInterval k r).Contains m) ∨
    ((exactInterval k r).upper = none ∧
      ∀ m, stoppingTime (2 ^ k * m + r) k ↔ (exactInterval k r).lower ≤ m) := by
  by_cases hne : ∃ m, (exactInterval k r).Contains m
  · have hu := upper_none_of_nonempty_le_256 hk hne
    right
    refine ⟨hu, fun m => ?_⟩
    rw [← exactInterval_spec, IndexInterval.Contains, hu]
    simp
  · left
    exact fun m hm => hne ⟨m, hm⟩

end Collatz.Research.CoefficientDescent
