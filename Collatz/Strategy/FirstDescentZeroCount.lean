import Collatz.Strategy.FirstDescentResidue
import Collatz.Core.Sum

/-!
# Exact finite counts of residue-zero first-descent landings

A bounded one-step computation detects every possible residue-zero first
descent. This special decision procedure is complete without assuming that
all odd inputs have a stopping time. Inputs are counted on `[1,N]`.
-/

namespace Collatz.FirstDescentResidue
open Collatz.Sum

/-- One-step executable detector for a residue-zero first descent. -/
def zeroLandingB (n : Nat) : Bool :=
  decide (0 < n ∧ acceleratedStep n < n ∧ acceleratedStep n % 3 = 0)

/-- Divisibility by three of the next state is exactly divisibility by six now. -/
theorem step_three_iff_six (n : Nat) : 3 ∣ acceleratedStep n ↔ 6 ∣ n := by
  simpa only [Nat.mul_one] using ThreeAdicEscape.pullback_divisibility n 1

/-- Exact arithmetic characterization of the executable detector. -/
theorem zeroLandingB_true_iff (n : Nat) :
    zeroLandingB n = true ↔ 0 < n ∧ 6 ∣ n := by
  simp only [zeroLandingB, decide_eq_true_eq]
  constructor
  · rintro ⟨hn, _, hz⟩
    exact ⟨hn, (step_three_iff_six n).mp (Nat.dvd_of_mod_eq_zero hz)⟩
  · rintro ⟨hn, h6⟩
    have hs := (step_three_iff_six n).mpr h6
    obtain ⟨q, hq⟩ := h6
    have he : n % 2 = 0 := by rw [hq]; omega
    have hd := (stoppingTime_of_even hn he).2.1
    exact ⟨hn, hd, Nat.mod_eq_zero_of_dvd hs⟩

/-- Soundness and completeness for the actual existential first-descent statement. -/
theorem zeroLandingB_spec {n : Nat} (hn : 0 < n) :
    zeroLandingB n = true ↔ ∃ k : Nat, stoppingTime n k ∧ 3 ∣ acceleratedOrbit k n := by
  rw [zeroLandingB_true_iff, exists_zero_landing_iff hn]
  simp only [hn, true_and]

/-- Count residue-zero first-descent landings from positive inputs at most N. -/
def zeroLandingCount (N : Nat) : Nat :=
  sumRange N (fun i => if zeroLandingB (i + 1) then 1 else 0)

/-- Positive residue-zero landing counts reduce to counting multiples of six. -/
theorem zeroLandingCount_as_multiples (N : Nat) :
    zeroLandingCount N = sumRange N (fun i => if (i + 1) % 6 = 0 then 1 else 0) := by
  unfold zeroLandingCount
  apply sumRange_congr
  intro i _
  have h : zeroLandingB (i + 1) = true ↔ (i + 1) % 6 = 0 := by
    rw [zeroLandingB_true_iff, Nat.dvd_iff_mod_eq_zero]
    simp only [Nat.zero_lt_succ, true_and]
  simp only [h]

/-- Exact count on every inclusive positive input cutoff. -/
theorem zeroLandingCount_exact (N : Nat) : zeroLandingCount N = N / 6 := by
  rw [zeroLandingCount_as_multiples]
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [sumRange_succ, ih]
    split <;> omega

/-- Each block of six positive inputs contributes exactly one zero landing. -/
theorem zeroLandingCount_aligned (q : Nat) : zeroLandingCount (6 * q) = q := by
  rw [zeroLandingCount_exact]
  omega

/-- At most one sixth of all inputs can first descend into residue zero. -/
theorem zeroLandingCount_sixfold_bound (N : Nat) : 6 * zeroLandingCount N ≤ N := by
  rw [zeroLandingCount_exact]
  omega

/-- The count has a remainder error strictly smaller than six. -/
theorem zeroLandingCount_remainder (N : Nat) :
    6 * zeroLandingCount N ≤ N ∧ N < 6 * zeroLandingCount N + 6 := by
  rw [zeroLandingCount_exact]
  omega

/-- The detector excludes the totalized zero state. -/
theorem zeroLandingB_zero : zeroLandingB 0 = false := by decide

/-- A finite regression exercising all branches of the detector. -/
theorem zeroLandingCount_sixty : zeroLandingCount 60 = 10 := by decide

end Collatz.FirstDescentResidue
