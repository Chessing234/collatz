import Collatz.Papers.Tao2022

/-!
# Semantic checks for the recorded logarithmic-density statement

The empty set must not have density one. This elementary negative test would
not detect a proof of Tao's theorem, but it detects the old vacuous True
placeholder. All weights below concern positive integers and all calculations
are checked in the kernel.
-/

namespace Collatz.Papers.Tao2022

/-- Appending the next positive integer adds precisely its harmonic weight. -/
theorem harmonicMass_succ (P : Nat → Prop) (N : Nat) [Decidable (P (N+1))] :
    harmonicMass P (N+1) = harmonicMass P N +
      (if P (N+1) then (1 : Rat) / ((N+1 : Nat) : Rat) else 0) := by
  classical
  by_cases hp : P (N+1) <;>
    simp [harmonicMass, List.range_succ, List.map_append, List.sum_append, Rat.add_zero, hp]

/-- Every positive-integer reciprocal is strictly positive. -/
theorem reciprocal_pos (n : Nat) (hn : 0 < n) : 0 < (1 : Rat) / (n : Rat) := by
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.inv_pos.mpr (Rat.natCast_pos.mpr hn)

/-- Arbitrary sets have nonnegative harmonic weight. -/
theorem harmonicMass_nonneg (P : Nat → Prop) (N : Nat) : 0 ≤ harmonicMass P N := by
  classical
  induction N with
  | zero => rw [harmonicMass_zero]; exact Rat.le_refl
  | succ N ih =>
    rw [harmonicMass_succ]
    split
    · exact Rat.add_nonneg ih (Rat.le_of_lt (reciprocal_pos _ (by omega)))
    · simpa only [Rat.add_zero] using ih

/-- The full harmonic weight is positive at every positive cutoff. -/
theorem harmonicMass_full_pos (N : Nat) (hn : 0 < N) :
    0 < harmonicMass (fun _ => True) N := by
  cases N with
  | zero => omega
  | succ N =>
    rw [harmonicMass_succ, if_pos trivial]
    have hp := reciprocal_pos (N+1) (by omega)
    have hz := harmonicMass_nonneg (fun _ => True) N
    have hle : (1 : Rat) / ((N+1 : Nat) : Rat) ≤
        harmonicMass (fun _ => True) N + 1 / ((N+1 : Nat) : Rat) := by
      simpa only [Rat.zero_add] using
        (Rat.add_le_add_right (c := (1 : Rat) / ((N+1 : Nat) : Rat))).mpr hz
    apply Rat.not_le.mp
    intro h
    exact Rat.not_le.mpr hp (Rat.le_trans hle h)

/-- In particular the repaired density predicate rejects the empty set. -/
theorem not_logDensityOne_empty : ¬ LogDensityOne (fun _ => False) := by
  intro h
  obtain ⟨N0, hN⟩ := h (mkRat 1 2) (by decide +kernel)
  have hm := hN (N0+1) (by omega) (by omega)
  rw [harmonicMass_empty] at hm
  have hp : 0 < (1 - mkRat 1 2) * harmonicMass (fun _ => True) (N0+1) :=
    Rat.mul_pos (by decide +kernel) (harmonicMass_full_pos _ (by omega))
  exact Rat.not_le.mpr hp hm

/-- Inclusion of sets gives inclusion of their harmonic weights. -/
theorem harmonicMass_mono (P Q : Nat → Prop) (hPQ : ∀ n, P n → Q n) (N : Nat) :
    harmonicMass P N ≤ harmonicMass Q N := by
  classical
  induction N with
  | zero => rw [harmonicMass_zero, harmonicMass_zero]; exact Rat.le_refl
  | succ N ih =>
    rw [harmonicMass_succ, harmonicMass_succ]
    by_cases hp : P (N+1)
    · rw [if_pos hp, if_pos (hPQ _ hp)]
      exact Rat.add_le_add_right.mpr ih
    · rw [if_neg hp, Rat.add_zero]
      by_cases hq : Q (N+1)
      · rw [if_pos hq]
        have hweight := Rat.le_of_lt (reciprocal_pos (N+1) (by omega))
        have hle : harmonicMass Q N ≤ harmonicMass Q N + 1 / ((N+1 : Nat) : Rat) := by
          simpa only [Rat.add_zero] using Rat.add_le_add_left.mpr hweight
        exact Rat.le_trans ih hle
      · simpa only [if_neg hq, Rat.add_zero] using ih

/-- A superset of a logarithmic-density-one set has logarithmic density one. -/
theorem logDensityOne_mono (P Q : Nat → Prop) (hPQ : ∀ n, P n → Q n)
    (hP : LogDensityOne P) : LogDensityOne Q := by
  intro eps heps
  obtain ⟨N0, hN⟩ := hP eps heps
  refine ⟨N0, ?_⟩
  intro N hge hpos
  exact Rat.le_trans (hN N hge hpos) (harmonicMass_mono P Q hPQ N)

/-- Orbit-bound sets are monotone in their bounds. -/
theorem orbitBelow_mono {n : Nat} {a b : Rat} (hab : a ≤ b) (ha : OrbitBelow n a) :
    OrbitBelow n b := by
  obtain ⟨k, hk⟩ := ha
  exact ⟨k, Rat.le_trans hk hab⟩

/-- Increasing a growth bound preserves its almost-everywhere orbit conclusion. -/
theorem almostBelow_mono (f g : Nat → Rat) (hfg : ∀ n, f n ≤ g n)
    (hf : LogDensityOne (fun n => OrbitBelow n (f n))) :
    LogDensityOne (fun n => OrbitBelow n (g n)) :=
  logDensityOne_mono _ _ (fun n hn => orbitBelow_mono (hfg n) hn) hf

end Collatz.Papers.Tao2022
