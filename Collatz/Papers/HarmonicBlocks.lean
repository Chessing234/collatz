import Collatz.Papers.TaoDensityChecks

/-!
# Quantitative harmonic blocks for logarithmic-density arguments

The harmonic mass used in the Tao statement cannot remain bounded: each
interval (N,2N] contributes at least 1/2. This file derives that estimate
from positive rational arithmetic and the finite-sum recurrence. No analytic
or Collatz convergence theorem is assumed.
-/

namespace Collatz.Papers.Tao2022

/-- Inversion reverses comparison between positive rationals. -/
theorem positive_inv_antitone {a b : Rat} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hai := Rat.le_of_lt (Rat.inv_pos.mpr ha)
  have hbi := Rat.le_of_lt (Rat.inv_pos.mpr hb)
  have hm := Rat.mul_le_mul_of_nonneg_left hab hai
  have ht := Rat.mul_le_mul_of_nonneg_right hm hbi
  calc
    b⁻¹ = (a⁻¹*a)*b⁻¹ := by rw [Rat.inv_mul_cancel _ (Rat.ne_of_gt ha), Rat.one_mul]
    _ ≤ (a⁻¹*b)*b⁻¹ := ht
    _ = a⁻¹ := by rw [Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt hb), Rat.mul_one]

/-- Larger positive natural denominators give smaller reciprocal weights. -/
theorem reciprocal_antitone {a b : Nat} (ha : 0 < a) (hab : a ≤ b) :
    (1 : Rat) / (b : Rat) ≤ 1 / (a : Rat) := by
  simp only [Rat.div_def, Rat.one_mul]
  exact positive_inv_antitone (Rat.natCast_pos.mpr ha)
    (Rat.natCast_pos.mpr (by omega)) (Rat.natCast_le_natCast.mpr hab)

/-- A block of L terms, all with denominators at most D, contributes at least L/D. -/
theorem harmonic_block_lower (N L D : Nat) (hD : N+L ≤ D) :
    harmonicMass (fun _ => True) N + (L : Rat) * (1 / (D : Rat)) ≤
      harmonicMass (fun _ => True) (N+L) := by
  induction L with
  | zero => simpa only [Nat.add_zero, Rat.natCast_ofNat, Rat.zero_mul, Rat.add_zero] using
      (Rat.le_refl (a := harmonicMass (fun _ => True) N))
  | succ L ih =>
    have hrec := ih (by omega)
    have hw := reciprocal_antitone (a := N+L+1) (b := D) (by omega) (by omega)
    have h1 := (Rat.add_le_add_right (c := (1 : Rat)/(D : Rat))).mpr hrec
    have h2 := (Rat.add_le_add_left (c := harmonicMass (fun _ => True) (N+L))).mpr hw
    have hfinal := Rat.le_trans h1 h2
    have he : N+(L+1) = (N+L)+1 := by omega
    rw [he, harmonicMass_succ, if_pos trivial]
    simpa only [Rat.natCast_add, Rat.natCast_ofNat, Rat.add_mul, Rat.one_mul,
      Rat.add_assoc] using hfinal

/-- Cancellation in the weight of a dyadic block, retaining an integer factor two. -/
theorem twice_block_weight (N : Nat) (hn : 0 < N) :
    (2 : Rat) * ((N : Rat) * (1 / ((2*N : Nat) : Rat))) = 1 := by
  have hz : (N : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hn)
  rw [Rat.natCast_mul, Rat.div_def, Rat.one_mul, Rat.inv_mul_rev]
  rw [← Rat.mul_assoc (N : Rat), Rat.mul_inv_cancel _ hz, Rat.one_mul]
  exact Rat.mul_inv_cancel 2 (by decide)

/-- Every dyadic block contributes at least one half to the full harmonic sum. -/
theorem harmonic_doubling (N : Nat) (hn : 0 < N) :
    (2 : Rat) * harmonicMass (fun _ => True) N + 1 ≤
      2 * harmonicMass (fun _ => True) (2*N) := by
  have hblock := harmonic_block_lower N N (2*N) (by omega)
  have hm := Rat.mul_le_mul_of_nonneg_left hblock (show (0 : Rat) ≤ 2 by decide)
  have he : N+N = 2*N := by omega
  rw [he, Rat.mul_add, twice_block_weight N hn] at hm
  exact hm

/-- Explicit logarithmic growth along powers of two: k ≤ 2 H(2^k). -/
theorem harmonic_pow_two_lower (k : Nat) :
    (k : Rat) ≤ 2 * harmonicMass (fun _ => True) (2^k) := by
  induction k with
  | zero =>
    simpa only [Rat.natCast_ofNat] using
      Rat.mul_nonneg (show (0 : Rat) ≤ 2 by decide) (harmonicMass_nonneg _ _)
  | succ k ih =>
    have hstep := harmonic_doubling (2^k) (Nat.pow_pos (by decide))
    have hinc := (Rat.add_le_add_right (c := 1)).mpr ih
    have ht := Rat.le_trans hinc hstep
    have he : (2:Nat)^(k+1) = 2*2^k := by rw [Nat.pow_succ, Nat.mul_comm]
    simpa only [Rat.natCast_add, Rat.natCast_ofNat, he] using ht

/-- Raising the cutoff can only increase the weight of any set. -/
theorem harmonicMass_cutoff_mono (P : Nat → Prop) {N M : Nat} (hNM : N ≤ M) :
    harmonicMass P N ≤ harmonicMass P M := by
  classical
  induction M with
  | zero =>
    have hn : N = 0 := by omega
    subst hn
    exact Rat.le_refl
  | succ M ih =>
    by_cases h : N ≤ M
    · have hstep : harmonicMass P M ≤ harmonicMass P (M+1) := by
        rw [harmonicMass_succ]
        split
        · have hw := Rat.le_of_lt (reciprocal_pos (M+1) (by omega))
          simpa only [Rat.add_zero] using Rat.add_le_add_left.mpr hw
        · rw [Rat.add_zero]; exact Rat.le_refl
      exact Rat.le_trans (ih h) hstep
    · have hn : N = M+1 := by omega
      subst hn
      exact Rat.le_refl

/-- A concrete cutoff for each natural harmonic-mass threshold. -/
theorem harmonic_at_exp_bound (K : Nat) :
    (K : Rat) ≤ harmonicMass (fun _ => True) (2^(2*K)) := by
  have h := harmonic_pow_two_lower (2*K)
  rw [Rat.natCast_mul, Rat.natCast_ofNat] at h
  exact Rat.le_of_mul_le_mul_left h (by decide)

/-- The full harmonic mass eventually exceeds every prescribed natural bound.
This establishes the unbounded normalization used in logarithmic density. -/
theorem harmonic_eventually_large (K : Nat) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
      (K : Rat) ≤ harmonicMass (fun _ => True) N := by
  refine ⟨2^(2*K), ?_⟩
  intro N hN
  exact Rat.le_trans (harmonic_at_exp_bound K) (harmonicMass_cutoff_mono _ hN)

/-- Rational thresholds follow by taking a nonnegative integer ceiling. -/
theorem harmonic_eventually_large_rat (R : Rat) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
      R ≤ harmonicMass (fun _ => True) N := by
  have hceil : R ≤ (R.ceil.toNat : Rat) := by
    apply Rat.le_trans Rat.le_ceil
    simpa only [Rat.intCast_natCast] using
      Rat.intCast_le_intCast.mpr (Int.self_le_toNat R.ceil)
  obtain ⟨N0, hN⟩ := harmonic_eventually_large R.ceil.toNat
  exact ⟨N0, fun N h => Rat.le_trans hceil (hN N h)⟩

end Collatz.Papers.Tao2022
