import CollatzTargetDensity.ShadowOscillation

/-! Quantitative separation from every periodic shadow pattern.
This excludes asymptotically periodic bounded shadows, not arbitrary bounded
aperiodic shadows and not arbitrary divergent integer orbits. -/
namespace CollatzTargetDensity.ShadowRigidity
open Erdos1135 OrbitReciprocals InverseBoundary BoundaryLinearization ShadowOscillation Filter
open scoped BigOperators Topology
noncomputable section

/-- Full valuation itineraries distinguish odd natural-number starts. -/
theorem same_valuations_implies_equal {n m : ℕ} (hn : Odd n) (hm : Odd m)
    (h : ∀ k, Tao.syracuseExponent (orbit n k) = Tao.syracuseExponent (orbit m k)) : n = m := by
  have htotal (k : ℕ) : valuationTotal n k = valuationTotal m k := by
    unfold valuationTotal
    exact Finset.sum_congr rfl (fun i _ => h i)
  have hinv : inverseSum2 n = inverseSum2 m := by
    funext k
    simp only [inverseSum2, scale2, htotal]
  have hlim : Tendsto (inverseSum2 m) atTop (nhds (-(n : ℚ_[2]))) := by
    simpa only [hinv] using inverseSum2_tendsto hn
  have he := tendsto_nhds_unique hlim (inverseSum2_tendsto hm)
  have he' : (n : ℚ_[2]) = (m : ℚ_[2]) := neg_injective he
  exact_mod_cast he'

theorem no_eventually_periodic_valuations {n : ℕ} (hn : Odd n)
    (hi : Function.Injective (orbit n)) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    ¬ ∀ k ≥ N, Tao.syracuseExponent (orbit n (k + p)) = Tao.syracuseExponent (orbit n k) := by
  intro h
  have he : orbit n N = orbit n (N + p) := by
    apply same_valuations_implies_equal (orbit_odd hn N) (orbit_odd hn (N + p))
    intro k
    simp only [orbit_shift]
    simpa only [Nat.add_assoc] using (h (k + N) (by omega)).symm
  have := hi he
  omega

/-- A scalar separation estimate for the integer coefficients in the
shadow recurrence. The tolerance depends only on the upper bound M. -/
theorem coefficient_eq_of_close {c d : ℕ} {x y u v M ε : ℝ}
    (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hc : (c : ℝ) * u = 3 * x - 1) (hd : (d : ℝ) * v = 3 * y - 1)
    (hcM : (c : ℝ) ≤ 3 * M) (hdM : (d : ℝ) ≤ 3 * M)
    (hε : 0 < ε) (hbudget : (3 + 3 * M) * ε < 1)
    (hxy : |y - x| < ε) (huv : |v - u| < ε) : c = d := by
  have rule {c d : ℕ} {x y u v : ℝ}
      (hv : 1 ≤ v) (hc : (c : ℝ) * u = 3 * x - 1)
      (hd : (d : ℝ) * v = 3 * y - 1) (hcM : (c : ℝ) ≤ 3 * M)
      (hxy : y - x < ε) (huv : u - ε < v) : ¬ c < d := by
    intro hcd
    have hcdR : (c : ℝ) + 1 ≤ d := by exact_mod_cast hcd
    have hprod := mul_le_mul_of_nonneg_right hcdR (by linarith : 0 ≤ v)
    have hclose := mul_le_mul_of_nonneg_left huv.le (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
    have hcoef := mul_le_mul_of_nonneg_right hcM hε.le
    nlinarith
  rcases lt_trichotomy c d with hlt | heq | hgt
  · exact False.elim (rule hv hc hd hcM (abs_lt.mp hxy).2 (by
      have := (abs_lt.mp huv).1; linarith) hlt)
  · exact heq
  · exact False.elim (rule hu hd hc hdM (by
      have := (abs_lt.mp hxy).1; linarith) (by
      have := (abs_lt.mp huv).2; linarith) hgt)

/-- Close neighboring shadow pairs force equal actual division exponents. -/
theorem valuation_eq_of_shadow_close {n : ℕ} (hn : Odd n)
    (hi : Function.Injective (orbit n)) {M ε : ℝ}
    (hbound : ∀ k, shadow (orbit n k) ≤ M)
    (hε : 0 < ε) (hbudget : (3 + 3 * M) * ε < 1) (i j : ℕ)
    (h0 : |shadow (orbit n j) - shadow (orbit n i)| < ε)
    (h1 : |shadow (orbit n (j + 1)) - shadow (orbit n (i + 1))| < ε) :
    Tao.syracuseExponent (orbit n i) = Tao.syracuseExponent (orbit n j) := by
  have hlow (k : ℕ) : 1 ≤ shadow (orbit n k) :=
    shadow_ge_one (orbit_odd hn k) (injective_shift hi k)
  have hstep (k : ℕ) : ((2 ^ Tao.syracuseExponent (orbit n k) : ℕ) : ℝ) *
      shadow (orbit n (k + 1)) = 3 * shadow (orbit n k) - 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, orbit_succ] using
      shadow_step (orbit_pos hn.pos k) (injective_shift hi k)
  have hcoeff (k : ℕ) : ((2 ^ Tao.syracuseExponent (orbit n k) : ℕ) : ℝ) ≤ 3 * M := by
    have hmul := mul_le_mul_of_nonneg_left (hlow (k + 1))
      (Nat.cast_nonneg (2 ^ Tao.syracuseExponent (orbit n k)) :
        (0 : ℝ) ≤ ((2 ^ Tao.syracuseExponent (orbit n k) : ℕ) : ℝ))
    have hs := hstep k
    have hb := hbound k
    nlinarith
  have he := coefficient_eq_of_close (hlow (i + 1)) (hlow (j + 1))
    (hstep i) (hstep j) (hcoeff i) (hcoeff j) hε hbudget h0 h1
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) he

/-- For every positive period p and every tail, a bounded shadow differs
from its p-step shift by at least the fixed amount 1/(6(M+1)). In particular
it cannot become asymptotically p-periodic for any p. -/
theorem quantitative_shift_separation {n : ℕ} (hn : Odd n)
    (hi : Function.Injective (orbit n)) {M : ℝ} (hM : 1 ≤ M)
    (hbound : ∀ k, shadow (orbit n k) ≤ M) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    ∃ k ≥ N, 1 / (6 * (M + 1)) ≤ |shadow (orbit n (k + p)) - shadow (orbit n k)| := by
  by_contra! h
  apply no_eventually_periodic_valuations hn hi hp N
  intro k hk
  have hε : (0 : ℝ) < 1 / (6 * (M + 1)) := by positivity
  have hbudget : (3 + 3 * M) * (1 / (6 * (M + 1))) < 1 := by
    rw [mul_one_div]
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < 6 * (M + 1))).2
    linarith
  have he := valuation_eq_of_shadow_close hn hi hbound hε hbudget k (k + p)
    (h k hk) (by simpa only [Nat.add_right_comm] using h (k + 1) (by omega))
  exact he.symm

theorem shadow_shift_not_tendsto_zero {n : ℕ} (hn : Odd n)
    (hi : Function.Injective (orbit n)) {M : ℝ} (hM : 1 ≤ M)
    (hbound : ∀ k, shadow (orbit n k) ≤ M) {p : ℕ} (hp : 0 < p) :
    ¬ Tendsto (fun k => shadow (orbit n (k + p)) - shadow (orbit n k)) atTop (nhds 0) := by
  intro h
  have habs := h.abs
  have hε : (0 : ℝ) < 1 / (6 * (M + 1)) := by positivity
  have hsmall := (tendsto_order.mp habs).2 (1 / (6 * (M + 1))) (by simpa using hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  obtain ⟨k, hk, hlarge⟩ := quantitative_shift_separation hn hi hM hbound hp N
  exact (not_lt_of_ge hlarge) (hN k hk)

/-- A close return bounds the first division coefficient through the whole
block budget. No upper bound on the shadow itself is needed. -/
theorem coefficient_bound_of_close_return {n : ℕ} (hn : Odd n)
    (hi : Function.Injective (orbit n)) {p : ℕ} (hp : 0 < p)
    (hclose : |shadow (orbit n p) - shadow n| < 1) :
    (2 : ℝ) ^ Tao.syracuseExponent n < 2 * (3 : ℝ) ^ p := by
  have hlow := shadow_ge_one (orbit_odd hn p) (injective_shift hi p)
  have hpos : 0 < shadow (orbit n p) := by linarith
  have hstart : shadow n < 2 * shadow (orbit n p) := by
    have := (abs_lt.mp hclose).1
    linarith
  have hrem : (n : ℝ) ≤ scale n p * (orbit n p : ℝ) := remainder_ge_start n p
  have hbudget : scale n p * shadow (orbit n p) ≤ shadow n := by
    unfold shadow
    rw [mul_sub, boundary_transport hn.pos hi]
    linarith
  rw [scale, div_mul_eq_mul_div] at hbudget
  have hblock := (div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ p)).mp hbudget
  have hmult : (3 : ℝ) ^ p * shadow n < (2 * (3 : ℝ) ^ p) * shadow (orbit n p) := by
    calc
      _ < (3 : ℝ) ^ p * (2 * shadow (orbit n p)) :=
        mul_lt_mul_of_pos_left hstart (by positivity)
      _ = _ := by ring
  have htotal : (2 : ℝ) ^ valuationTotal n p < 2 * (3 : ℝ) ^ p :=
    (mul_lt_mul_iff_left₀ hpos).mp (hblock.trans_lt (by simpa [mul_comm] using hmult))
  have hfirst : Tao.syracuseExponent n ≤ valuationTotal n p := by
    have h := Finset.single_le_sum
      (f := fun i => Tao.syracuseExponent (orbit n i))
      (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hp)
    simpa only [valuationTotal, orbit, Function.iterate_zero, id_eq] using h
  exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hfirst).trans_lt htotal

/-- Uniform separation from every fixed-period shift, even when the shadow
is unbounded. The explicit tolerance depends only on the proposed period. -/
theorem unconditional_shift_separation {n : ℕ} (hn : Odd n)
    (hi : Function.Injective (orbit n)) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    ∃ k ≥ N, 1 / (2 * (3 + 2 * (3 : ℝ) ^ p)) ≤
      |shadow (orbit n (k + p)) - shadow (orbit n k)| := by
  let C : ℝ := 2 * (3 : ℝ) ^ p
  let ε : ℝ := 1 / (2 * (3 + C))
  have hC : 0 < C := by dsimp [C]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεone : ε < 1 := by
    dsimp [ε]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (3 + C))).2
    linarith
  have hbudget : (3 + 3 * (C / 3)) * ε < 1 := by
    dsimp [ε]
    rw [mul_one_div]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (3 + C))).2
    linarith
  by_contra! h
  apply no_eventually_periodic_valuations hn hi hp N
  have hcoeff (k : ℕ) (hk : N ≤ k) :
      ((2 ^ Tao.syracuseExponent (orbit n k) : ℕ) : ℝ) ≤ 3 * (C / 3) := by
    have hc : |shadow (orbit (orbit n k) p) - shadow (orbit n k)| < 1 := by
      rw [orbit_shift, Nat.add_comm p k]
      exact (h k hk).trans hεone
    have hb := coefficient_bound_of_close_return (orbit_odd hn k) (injective_shift hi k) hp hc
    have hb' : ((2 ^ Tao.syracuseExponent (orbit n k) : ℕ) : ℝ) < C := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, C] using hb
    linarith
  have hlow (k : ℕ) : 1 ≤ shadow (orbit n k) :=
    shadow_ge_one (orbit_odd hn k) (injective_shift hi k)
  have hstep (k : ℕ) : ((2 ^ Tao.syracuseExponent (orbit n k) : ℕ) : ℝ) *
      shadow (orbit n (k + 1)) = 3 * shadow (orbit n k) - 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, orbit_succ] using
      shadow_step (orbit_pos hn.pos k) (injective_shift hi k)
  intro k hk
  have he := coefficient_eq_of_close (hlow (k + 1)) (hlow (k + p + 1))
    (hstep k) (hstep (k + p)) (hcoeff k hk) (hcoeff (k + p) (by omega))
    hε hbudget (h k hk) (by simpa only [Nat.add_right_comm] using h (k + 1) (by omega))
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2) he).symm

/-- No divergent odd integer orbit has an asymptotically periodic shadow,
in the sense of vanishing absolute error under any fixed positive shift. -/
theorem no_asymptotic_shadow_period {n : ℕ} (hn : Odd n)
    (hi : Function.Injective (orbit n)) {p : ℕ} (hp : 0 < p) :
    ¬ Tendsto (fun k => shadow (orbit n (k + p)) - shadow (orbit n k)) atTop (nhds 0) := by
  intro h
  have habs := h.abs
  have hε : (0 : ℝ) < 1 / (2 * (3 + 2 * (3 : ℝ) ^ p)) := by positivity
  have hsmall := (tendsto_order.mp habs).2 (1 / (2 * (3 + 2 * (3 : ℝ) ^ p)))
    (by simpa using hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  obtain ⟨k, hk, hlarge⟩ := unconditional_shift_separation hn hi hp N
  exact (not_lt_of_ge hlarge) (hN k hk)

end
end CollatzTargetDensity.ShadowRigidity
