import Collatz.Research.StoppingAtlas.Horizon

/-! Transfer the interval-shape theorem through any certified crossing horizon. -/
namespace Collatz.Research.StoppingAtlas
open FirstLightDescent FirstLightConsequences CoefficientDescent DescentIntervals

/-- A crossing certificate supplies the existing exact-stopping predicate. -/
theorem stopping_iff_firstLight {H n k : Nat} (hH : ExactThrough H)
    (hn : 1 < n) (hk : k ≤ H) : stoppingTime n k ↔ FirstLight n k :=
  stopping_iff_firstLight_of_horizon hH hn hk

/-- Every bounded nonempty exact-time class is beyond any certified horizon. -/
theorem finite_interval_beyond {H k r : Nat} (hH : ExactThrough H)
    (hb : ∃ B, ∀ m, (exactInterval k r).Contains m → m < B)
    (hne : ∃ m, (exactInterval k r).Contains m) : H < k := by
  obtain ⟨n, hn, hs, hf⟩ := finite_interval_witness hb hne
  by_cases hk : k ≤ H
  · exact False.elim (hf ((stopping_iff_firstLight hH hn hk).mp hs))
  · omega

/-- Class indices are upward closed through an arbitrary certified horizon. -/
theorem membership_upward {H k r m u : Nat} (hH : ExactThrough H) (hk : k ≤ H)
    (hmu : m ≤ u) (hs : (exactInterval k r).Contains m) :
    (exactInterval k r).Contains u := by
  have hd := (exactInterval_spec k r m).mp hs
  have hn := start_gt_one hd
  have hf := (stopping_iff_firstLight hH hn hk).mp hd
  have hr := (firstLight_class k r m).mp hf
  have hmul := Nat.mul_le_mul_left (2 ^ k) hmu
  have hnu : 1 < 2 ^ k * u + r := by omega
  exact (exactInterval_spec k r u).mpr
    ((stopping_iff_firstLight hH hnu hk).mpr ((firstLight_class k r u).mpr hr))

/-- A nonempty exact-time interval below a certified horizon has infinite upper endpoint. -/
theorem upper_none {H k r : Nat} (hH : ExactThrough H) (hk : k ≤ H)
    (hne : ∃ m, (exactInterval k r).Contains m) : (exactInterval k r).upper = none := by
  cases hu : (exactInterval k r).upper with
  | none => rfl
  | some B =>
    have hb : ∃ B, ∀ m, (exactInterval k r).Contains m → m < B := by
      refine ⟨B, ?_⟩
      intro m hm
      have h := hm.2
      simpa only [hu] using h
    have := finite_interval_beyond hH hb hne
    omega

/-- Complete interval-shape classification, parametrized by a proof rather than a literal horizon. -/
theorem empty_or_tail {H : Nat} (hH : ExactThrough H) (k r : Nat) (hk : k ≤ H) :
    (∀ m, ¬ (exactInterval k r).Contains m) ∨
    ((exactInterval k r).upper = none ∧
      ∀ m, stoppingTime (2 ^ k * m + r) k ↔ (exactInterval k r).lower ≤ m) := by
  by_cases hne : ∃ m, (exactInterval k r).Contains m
  · have hu := upper_none hH hk hne
    right
    refine ⟨hu, fun m => ?_⟩
    rw [← exactInterval_spec, IndexInterval.Contains, hu]
    simp
  · exact Or.inl (fun m hm => hne ⟨m, hm⟩)

/-- The census phenomenon holds at all representatives and indices through 1538. -/
theorem empty_or_tail_1538 (k r : Nat) (hk : k ≤ 1538) :
    (∀ m, ¬ (exactInterval k r).Contains m) ∨
    ((exactInterval k r).upper = none ∧
      ∀ m, stoppingTime (2 ^ k * m + r) k ↔ (exactInterval k r).lower ≤ m) :=
  empty_or_tail exactThrough_1538 k r hk

end Collatz.Research.StoppingAtlas
