import CollatzTargetDensity.InverseBoundary
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! The same inverse-affine remainder in the 2-adic topology.
Its vanishing here must not be transferred to the real topology. -/
namespace CollatzTargetDensity.InverseBoundary
open Erdos1135 OrbitReciprocals Filter
open scoped BigOperators Topology
noncomputable section

def scale2 (n k : ℕ) : ℚ_[2] := (2 : ℚ_[2]) ^ valuationTotal n k / (3 : ℚ_[2]) ^ k

def remainder2 (n k : ℕ) : ℚ_[2] := scale2 n k * (orbit n k : ℚ_[2])

def inverseSum2 (n k : ℕ) : ℚ_[2] := ∑ i ∈ Finset.range k, scale2 n i / 3

theorem scale2_succ (n k : ℕ) :
    scale2 n (k + 1) = scale2 n k * (2 : ℚ_[2]) ^ Tao.syracuseExponent (orbit n k) / 3 := by
  simp only [scale2, valuationTotal, Finset.sum_range_succ, pow_add, pow_succ]
  ring

theorem remainder2_succ (n k : ℕ) :
    remainder2 n (k + 1) = remainder2 n k + scale2 n k / 3 := by
  have he : (2 : ℚ_[2]) ^ Tao.syracuseExponent (orbit n k) * (orbit n (k + 1) : ℚ_[2]) =
      3 * (orbit n k : ℚ_[2]) + 1 := by
    have h := Tao.two_pow_syracuseExponent_mul_syracuse (orbit n k)
    rw [orbit_succ] at h
    exact_mod_cast h
  unfold remainder2
  rw [scale2_succ]
  calc
    _ = scale2 n k / 3 * ((2 : ℚ_[2]) ^ Tao.syracuseExponent (orbit n k) * orbit n (k + 1)) := by ring
    _ = scale2 n k / 3 * (3 * (orbit n k : ℚ_[2]) + 1) := by rw [he]
    _ = _ := by ring

theorem remainder2_eq_start_add_inverseSum (n k : ℕ) :
    remainder2 n k = (n : ℚ_[2]) + inverseSum2 n k := by
  induction k with
  | zero => simp [remainder2, scale2, valuationTotal, inverseSum2, orbit]
  | succ k ih => rw [remainder2_succ, ih]; simp [inverseSum2, Finset.sum_range_succ, add_assoc]

theorem orbit_odd {n : ℕ} (hn : Odd n) (i : ℕ) : Odd (orbit n i) := by
  cases i with
  | zero => exact hn
  | succ i => rw [← orbit_succ]; exact Tao.syracuse_odd _

theorem valuationTotal_ge_steps {n : ℕ} (hn : Odd n) (k : ℕ) : k ≤ valuationTotal n k := by
  induction k with
  | zero => simp [valuationTotal]
  | succ k ih =>
    have hv := Tao.syracuseExponent_pos_of_odd (orbit_odd hn k)
    simp only [valuationTotal, Finset.sum_range_succ] at *
    omega

theorem norm_three_two_adic : ‖(3 : ℚ_[2])‖ = 1 :=
  (Padic.norm_natCast_eq_one_iff (p := 2)).mpr (by decide : Nat.Coprime 2 3)

theorem norm_scale2 (n k : ℕ) : ‖scale2 n k‖ = (1 / 2 : ℝ) ^ valuationTotal n k := by
  have h2 : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by simpa using Padic.norm_p (p := 2)
  rw [scale2, norm_div, norm_pow, norm_pow, norm_three_two_adic, h2]
  simp

theorem norm_remainder2_le {n : ℕ} (hn : Odd n) (k : ℕ) :
    ‖remainder2 n k‖ ≤ (1 / 2 : ℝ) ^ k := by
  have ha : ‖(orbit n k : ℚ_[2])‖ ≤ 1 := by
    simpa only [Int.cast_natCast] using Padic.norm_int_le_one (p := 2) (orbit n k : ℤ)
  rw [remainder2, norm_mul, norm_scale2]
  calc
    _ ≤ (1 / 2 : ℝ) ^ valuationTotal n k * 1 :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ ≤ (1 / 2 : ℝ) ^ k := by
      rw [mul_one]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (valuationTotal_ge_steps hn k)

/-- Vanishing of the 2-adic remainder holds for every odd start, independently
of convergence, cycles, or injectivity of its forward orbit. -/
theorem remainder2_tendsto_zero {n : ℕ} (hn : Odd n) :
    Tendsto (remainder2 n) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (norm_remainder2_le hn)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-- The inverse series has 2-adic partial-sum limit minus the starting integer. -/
theorem inverseSum2_tendsto {n : ℕ} (hn : Odd n) :
    Tendsto (inverseSum2 n) atTop (nhds (-(n : ℚ_[2]))) := by
  have h := (remainder2_tendsto_zero hn).sub_const (n : ℚ_[2])
  simpa only [remainder2_eq_start_add_inverseSum, add_sub_cancel_left, zero_sub] using h

/-- Both conclusions are compatible: different completions of the rationals
give different boundary limits for one hypothetical injective orbit. -/
theorem two_topology_boundary_limits {n : ℕ} (hn : Odd n)
    (hi : Function.Injective (orbit n)) :
    0 < realBoundary n ∧
      Tendsto (remainder n) atTop (nhds (realBoundary n)) ∧
      Tendsto (remainder2 n) atTop (nhds 0) :=
  ⟨realBoundary_pos hn.pos, remainder_tendsto_realBoundary hn.pos hi, remainder2_tendsto_zero hn⟩

def rationalRemainder (n k : ℕ) : ℚ :=
  (2 : ℚ) ^ valuationTotal n k / (3 : ℚ) ^ k * (orbit n k : ℚ)

theorem rationalRemainder_real (n k : ℕ) : (rationalRemainder n k : ℝ) = remainder n k := by
  simp [rationalRemainder, remainder, scale]

theorem rationalRemainder_padic (n k : ℕ) : (rationalRemainder n k : ℚ_[2]) = remainder2 n k := by
  simp [rationalRemainder, remainder2, scale2]

/-- The two sequences are embeddings of the very same rational numbers. -/
theorem same_rational_remainders_two_limits {n : ℕ} (hn : Odd n)
    (hi : Function.Injective (orbit n)) :
    0 < realBoundary n ∧
      Tendsto (fun k => (rationalRemainder n k : ℝ)) atTop (nhds (realBoundary n)) ∧
      Tendsto (fun k => (rationalRemainder n k : ℚ_[2])) atTop (nhds 0) := by
  simpa only [rationalRemainder_real, rationalRemainder_padic] using two_topology_boundary_limits hn hi

end
end CollatzTargetDensity.InverseBoundary
