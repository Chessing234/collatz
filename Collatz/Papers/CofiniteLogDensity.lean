import Collatz.Papers.HarmonicBlocks

/-!
# Finite exceptions and the Collatz-to-Tao implication

Finite exceptional sets have bounded harmonic mass. Since full harmonic mass
diverges, every cofinite set has logarithmic density one. As a semantic check,
the full Collatz conjecture implies the recorded rational-valued Tao conclusion.
The converse and Tao's unconditional theorem are not proved here.
-/

namespace Collatz.Papers.Tao2022

/-- A set and its complement partition full harmonic mass exactly. -/
theorem harmonicMass_complement (P : Nat → Prop) (N : Nat) :
    harmonicMass P N + harmonicMass (fun n => ¬ P n) N =
      harmonicMass (fun _ => True) N := by
  classical
  induction N with
  | zero => simp only [harmonicMass_zero, Rat.add_zero]
  | succ N ih =>
    rw [harmonicMass_succ, harmonicMass_succ, harmonicMass_succ, if_pos trivial]
    by_cases hp : P (N+1)
    · rw [if_pos hp, if_neg (not_not_intro hp), Rat.add_zero]
      rw [Rat.add_assoc, Rat.add_comm (1 / ((N+1 : Nat) : Rat)), ← Rat.add_assoc, ih]
    · rw [if_neg hp, if_pos hp, Rat.add_zero, ← Rat.add_assoc, ih]

/-- Above its support cutoff a set's harmonic mass is constant. -/
theorem supported_mass_stable (P : Nat → Prop) (C : Nat)
    (hs : ∀ n, C < n → ¬ P n) (L : Nat) :
    harmonicMass P (C+L) = harmonicMass P C := by
  classical
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [Nat.add_succ, harmonicMass_succ, if_neg (hs _ (by omega)), Rat.add_zero, ih]

/-- A supported set has a uniform mass bound at every cutoff. -/
theorem supported_mass_bound (P : Nat → Prop) (C : Nat)
    (hs : ∀ n, C < n → ¬ P n) (N : Nat) :
    harmonicMass P N ≤ harmonicMass (fun _ => True) C := by
  have hfull := harmonicMass_mono P (fun _ => True) (fun _ _ => trivial) C
  by_cases hNC : N ≤ C
  · exact Rat.le_trans (harmonicMass_cutoff_mono P hNC) hfull
  · have he : N = C+(N-C) := by omega
    rw [he, supported_mass_stable P C hs]
    exact hfull

/-- Cofinite sets have logarithmic density one, with no orbit hypothesis. -/
theorem logDensityOne_of_cofinite (P : Nat → Prop) (C : Nat)
    (hP : ∀ n, C < n → P n) : LogDensityOne P := by
  intro eps heps
  obtain ⟨N0, hN⟩ := harmonic_eventually_large_rat
    (harmonicMass (fun _ => True) C / eps)
  refine ⟨N0, ?_⟩
  intro N hge _hpos
  have hbound := supported_mass_bound (fun n => ¬ P n) C
    (fun n hn => not_not_intro (hP n hn)) N
  have hm := Rat.mul_le_mul_of_nonneg_right (hN N hge) (Rat.le_of_lt heps)
  rw [Rat.div_mul_cancel (Rat.ne_of_gt heps)] at hm
  have hepsbound : harmonicMass (fun n => ¬ P n) N ≤
      eps * harmonicMass (fun _ => True) N := by
    rw [Rat.mul_comm]
    exact Rat.le_trans hbound hm
  have hsum := harmonicMass_complement P N
  have htotal : harmonicMass (fun _ => True) N ≤
      harmonicMass P N + eps * harmonicMass (fun _ => True) N := by
    calc
      harmonicMass (fun _ => True) N =
          harmonicMass P N + harmonicMass (fun n => ¬ P n) N := hsum.symm
      _ ≤ harmonicMass P N + eps * harmonicMass (fun _ => True) N :=
        Rat.add_le_add_left.mpr hepsbound
  have hshift := (Rat.add_le_add_right
    (c := -(eps * harmonicMass (fun _ => True) N))).mpr htotal
  simpa only [Rat.sub_eq_add_neg, Rat.add_mul, Rat.one_mul, Rat.neg_mul,
    Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero] using hshift

/-- Universal convergence supplies a nonvacuous sufficient condition for the
recorded almost-bounded statement. This theorem assumes Collatz explicitly. -/
theorem taoAlmostBoundedOrbits_of_collatz (hC : CollatzConjecture) :
    taoAlmostBoundedOrbits := by
  intro f hf
  obtain ⟨C, hCbound⟩ := hf 1
  apply logDensityOne_of_cofinite (fun n => OrbitBelow n (f n)) C
  intro n hn
  exact orbitBelow_of_reaches_one (hC n (by omega)) (hCbound n (by omega))

/-- Removing any one positive integer leaves logarithmic density one. -/
theorem densityOne_without_point (m : Nat) : LogDensityOne (fun n => n ≠ m) :=
  logDensityOne_of_cofinite _ m (fun n hn => by omega)

/-- Density one alone does not imply universal membership for arbitrary sets.
This is not a counterexample to Collatz and is not an independence theorem. -/
theorem density_one_not_universal :
    ∃ P : Nat → Prop, LogDensityOne P ∧ ¬ (∀ n, 0 < n → P n) := by
  refine ⟨fun n => n ≠ 2, densityOne_without_point 2, ?_⟩
  intro h
  exact h 2 (by omega) rfl

end Collatz.Papers.Tao2022
