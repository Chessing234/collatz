import CollatzTargetDensity.SyracuseEnergy
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!
Finite cost-generating polynomials and the actual Syracuse law.
The polynomial coefficients are natural-number path counts. The generating
function identity is a marginal identity, not a fixed-cost lower bound or
a proof of the Collatz conjecture.
-/
namespace CollatzTargetDensity.FixedCostGenerators
open Erdos1135 SyracuseEnergy
open scoped BigOperators
noncomputable section

def period (n : ℕ) : ℕ := 2 * 3 ^ n

theorem period_pos (n : ℕ) : 0 < period n := by unfold period; positivity

theorem two_pow_period (n : ℕ) :
    (2 : ZMod (3 ^ (n + 1))) ^ period n = 1 := by
  have hc : Nat.Coprime 2 (3 ^ (n + 1)) :=
    (by decide : Nat.Coprime 2 3).pow_right (n + 1)
  have h := Nat.ModEq.pow_totient hc
  have ht : Nat.totient (3 ^ (n + 1)) = period n := by
    rw [Nat.totient_prime_pow_succ (by decide : Nat.Prime 3)]
    simp [period, Nat.mul_comm]
  rw [ht] at h
  exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

def boundary (n : ℕ) (f : ZMod (3 ^ n) → ℝ)
    (r : ZMod (3 ^ (n + 1))) : ℝ :=
  ∑ y : ZMod (3 ^ n), if lift n y = r then f y else 0

def polynomialBoundary (n : ℕ) (f : ZMod (3 ^ n) → Polynomial ℕ)
    (r : ZMod (3 ^ (n + 1))) : Polynomial ℕ :=
  ∑ y : ZMod (3 ^ n), if lift n y = r then f y else 0

theorem lift_val (n : ℕ) (y : ZMod (3 ^ n)) : (lift n y).val = 3 * y.val + 1 := by
  have hy := ZMod.val_lt y
  have hlt : 3 * y.val + 1 < 3 ^ (n + 1) := by rw [pow_succ]; omega
  have he : lift n y = ((3 * y.val + 1 : ℕ) : ZMod (3 ^ (n + 1))) := by
    simp [lift]
  rw [he, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

/-- The finite residue sum equals the usual inverse-branch lookup.
The branch is absent unless its numerator is divisible by three. -/
theorem polynomialBoundary_explicit (n : ℕ) (f : ZMod (3 ^ n) → Polynomial ℕ)
    (r : ZMod (3 ^ (n + 1))) :
    polynomialBoundary n f r =
      if r.val % 3 = 1 then f ((r.val / 3 : ℕ) : ZMod (3 ^ n)) else 0 := by
  classical
  by_cases hr : r.val % 3 = 1
  · rw [if_pos hr]
    let z : ZMod (3 ^ n) := (r.val / 3 : ℕ)
    have hzval : z.val = r.val / 3 := by
      have hlt := ZMod.val_lt r
      have hpow := pow_succ 3 n
      have hd : r.val / 3 < 3 ^ n := by omega
      simpa only [z, ZMod.val_natCast] using Nat.mod_eq_of_lt hd
    have hz : lift n z = r := by
      apply ZMod.val_injective
      rw [lift_val, hzval]
      omega
    have he (y : ZMod (3 ^ n)) : lift n y = r ↔ y = z := by
      rw [← hz]
      exact (lift_injective n).eq_iff
    simp only [polynomialBoundary, he]
    simp [z]
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro y _
    have hne : lift n y ≠ r := by
      intro he
      have hv := congrArg ZMod.val he
      rw [lift_val] at hv
      omega
    simp [hne]

/-- Forward residue formulation of the finite inverse generator recursion.
The natural coefficients count paths of total cost k, with each stage's
exponent in one complete period. -/
def generator : (n : ℕ) → ZMod (3 ^ n) → Polynomial ℕ
  | 0, _ => 1
  | n + 1, r => ∑ j ∈ Finset.range (period n),
      Polynomial.X ^ j * polynomialBoundary n (generator n)
        ((2 : ZMod (3 ^ (n + 1))) ^ (j + 1) * r)

def value (n : ℕ) (r : ZMod (3 ^ n)) : ℝ :=
  (generator n r).eval₂ (Nat.castRingHom ℝ) (1 / 2)

theorem value_succ (n : ℕ) (r : ZMod (3 ^ (n + 1))) :
    value (n + 1) r = ∑ j ∈ Finset.range (period n),
      (1 / 2 : ℝ) ^ j * boundary n (value n)
        ((2 : ZMod (3 ^ (n + 1))) ^ (j + 1) * r) := by
  simp [value, generator, polynomialBoundary, boundary,
    Polynomial.eval₂_finset_sum, apply_ite]

theorem pmf_double_recurrence (n : ℕ) (r : ZMod (3 ^ (n + 1))) :
    (Tao.syracPMF (n + 1) r).toReal =
      ((Tao.syracPMF (n + 1) (2 * r)).toReal + inputMass n (2 * r)) / 2 := by
  have hi := Tao.taoZModThreePow_inv_two_pow_mul (n + 1) 1
  simp only [pow_one] at hi
  simpa only [half, ← mul_assoc, hi, one_mul] using pmf_half_recurrence n (2 * r)

/-- Finite unrolling retains the boundary term and the final remainder. -/
theorem pmf_unroll (n k : ℕ) (r : ZMod (3 ^ (n + 1))) :
    (Tao.syracPMF (n + 1) r).toReal =
      (1 / 2 : ℝ) ^ k *
        (Tao.syracPMF (n + 1) ((2 : ZMod (3 ^ (n + 1))) ^ k * r)).toReal +
      ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (j + 1) *
        inputMass n ((2 : ZMod (3 ^ (n + 1))) ^ (j + 1) * r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := pmf_double_recurrence n ((2 : ZMod (3 ^ (n + 1))) ^ k * r)
    have he : (2 : ZMod (3 ^ (n + 1))) * (2 ^ k * r) = 2 ^ (k + 1) * r := by
      rw [pow_succ (2 : ZMod (3 ^ (n + 1))) k]; ring
    rw [he] at h
    rw [Finset.sum_range_succ, pow_succ (1 / 2 : ℝ) k, ih, h]
    ring

theorem pmf_period_equation (n : ℕ) (r : ZMod (3 ^ (n + 1))) :
    (1 - (1 / 2 : ℝ) ^ period n) * (Tao.syracPMF (n + 1) r).toReal =
      ∑ j ∈ Finset.range (period n), (1 / 2 : ℝ) ^ (j + 1) *
        inputMass n ((2 : ZMod (3 ^ (n + 1))) ^ (j + 1) * r) := by
  have h := pmf_unroll n (period n) r
  rw [two_pow_period, one_mul] at h
  linarith

def geometricProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (1 - (1 / 2 : ℝ) ^ period i)

def normalizer (n : ℕ) : ℝ := (2 : ℝ) ^ n * geometricProduct n

theorem geometricProduct_pos (n : ℕ) : 0 < geometricProduct n := by
  apply Finset.prod_pos
  intro i _
  exact sub_pos.mpr (pow_lt_one₀ (by norm_num) (by norm_num) (period_pos i).ne')

theorem normalizer_pos (n : ℕ) : 0 < normalizer n := by
  exact mul_pos (by positivity) (geometricProduct_pos n)

theorem geometricProduct_le_one (n : ℕ) : geometricProduct n ≤ 1 := by
  apply Finset.prod_le_one
  · intro i _
    exact (sub_pos.mpr (pow_lt_one₀ (by norm_num) (by norm_num) (period_pos i).ne')).le
  · intro i _
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ period i := by positivity
    linarith

theorem period_ge_linear (n : ℕ) : 2 * (n + 1) ≤ period n := by
  have h : n + 1 ≤ 3 ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  unfold period
  omega

theorem period_tail_le (n : ℕ) :
    (1 / 2 : ℝ) ^ period n ≤ (1 / 4 : ℝ) ^ (n + 1) := by
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (period_ge_linear n)
  convert h using 1
  rw [pow_mul]
  norm_num

theorem period_tail_sum_le (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ period i) ≤
      (1 - (1 / 4 : ℝ) ^ n) / 3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h := period_tail_le n
    rw [pow_succ] at h
    linarith

theorem geometricProduct_ge_one_sub_sum (n : ℕ) :
    1 - (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ period i) ≤ geometricProduct n := by
  induction n with
  | zero => simp [geometricProduct]
  | succ n ih =>
    have hle := geometricProduct_le_one n
    have hnonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ period n := by positivity
    have hs : geometricProduct (n + 1) =
        geometricProduct n * (1 - (1 / 2 : ℝ) ^ period n) := by
      simp [geometricProduct, Finset.prod_range_succ]
    rw [Finset.sum_range_succ, hs]
    nlinarith

/-- A numerical lower bound for the full finite normalizing product. -/
theorem geometricProduct_ge_two_thirds (n : ℕ) : (2 / 3 : ℝ) ≤ geometricProduct n := by
  have hsum := period_tail_sum_le n
  have hprod := geometricProduct_ge_one_sub_sum n
  have hp : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ n := by positivity
  linarith

theorem normalizer_succ (n : ℕ) :
    normalizer (n + 1) = 2 * normalizer n * (1 - (1 / 2 : ℝ) ^ period n) := by
  simp only [normalizer, geometricProduct, Finset.prod_range_succ, pow_succ]
  ring

/-- Exact finite generating-function identity for the imported PMF. -/
theorem normalizer_mul_pmf_eq_value (n : ℕ) :
    ∀ r : ZMod (3 ^ n), normalizer n * (Tao.syracPMF n r).toReal = value n r := by
  induction n with
  | zero =>
    intro r
    have hr : r = 0 := by
      apply ZMod.val_injective
      have h := ZMod.val_lt r
      norm_num at h ⊢
      omega
    rw [hr, Tao.syracPMF_zero_apply_zero]
    simp [normalizer, geometricProduct, value, generator]
  | succ n ih =>
    intro r
    have hb (s : ZMod (3 ^ (n + 1))) :
        boundary n (value n) s = normalizer n * inputMass n s := by
      simp only [boundary, inputMass, Finset.mul_sum, mul_ite, mul_zero]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp_all
    have h := congrArg (fun x : ℝ => 2 * normalizer n * x) (pmf_period_equation n r)
    dsimp only at h
    rw [Finset.mul_sum] at h
    rw [value_succ]
    calc
      normalizer (n + 1) * (Tao.syracPMF (n + 1) r).toReal =
          2 * normalizer n * ((1 - (1 / 2 : ℝ) ^ period n) *
            (Tao.syracPMF (n + 1) r).toReal) := by rw [normalizer_succ]; ring
      _ = _ := h
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hb, pow_succ (1 / 2 : ℝ) j]
        ring

theorem pmf_eq_generator_value (n : ℕ) (r : ZMod (3 ^ n)) :
    (Tao.syracPMF n r).toReal =
      (generator n r).eval₂ (Nat.castRingHom ℝ) (1 / 2) /
        ((2 : ℝ) ^ n * geometricProduct n) := by
  apply (eq_div_iff (normalizer_pos n).ne').2
  simpa [normalizer, value, mul_comm] using normalizer_mul_pmf_eq_value n r

/-- The weighted residue sums have the expected exact normalization. -/
theorem sum_value_eq_normalizer (n : ℕ) :
    (∑ r : ZMod (3 ^ n), value n r) = normalizer n := by
  simp_rw [← normalizer_mul_pmf_eq_value]
  rw [← Finset.mul_sum, pmf_sum, mul_one]

/-- Unconditional weighted generator floor, uniform in depth and unit
residue. This controls evaluation at 1/2, not a specified coefficient. -/
theorem uniform_generator_value_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ZMod (3 ^ n),
      IsUnit r → c * (2 / 3 : ℝ) ^ n ≤ value n r := by
  obtain ⟨c, hc, hfloor⟩ := SyracuseMinorant.syracuse_uniform_atom_lower_bound
  refine ⟨(2 / 3) * c, by positivity, ?_⟩
  intro n hn r hr
  have h := mul_le_mul_of_nonneg_left (hfloor n hn r hr) (normalizer_pos n).le
  rw [normalizer_mul_pmf_eq_value] at h
  apply le_trans _ h
  have hd : (2 : ℝ) ^ n * (2 / 3) ≤ normalizer n :=
    mul_le_mul_of_nonneg_left (geometricProduct_ge_two_thirds n) (by positivity)
  have hm := mul_le_mul_of_nonneg_right hd (show (0 : ℝ) ≤ c / 3 ^ n by positivity)
  convert hm using 1
  rw [div_pow]
  ring

def count (n k : ℕ) (r : ZMod (3 ^ n)) : ℕ := (generator n r).coeff k

theorem count_succ (n k : ℕ) (r : ZMod (3 ^ (n + 1))) :
    count (n + 1) k r = ∑ j ∈ Finset.range (period n),
      if j ≤ k then ∑ y : ZMod (3 ^ n),
        if lift n y = (2 : ZMod (3 ^ (n + 1))) ^ (j + 1) * r
          then count n (k - j) y else 0
      else 0 := by
  simp [count, generator, polynomialBoundary, Polynomial.finset_sum_coeff,
    Polynomial.coeff_X_pow_mul', apply_ite, ite_apply]

theorem count_zero (k : ℕ) (r : ZMod (3 ^ 0)) :
    count 0 k r = if k = 0 then 1 else 0 := by
  simp [count, generator, Polynomial.coeff_one]

theorem sum_range_cutoff (c k : ℕ) (f : ℕ → ℕ) :
    (∑ j ∈ Finset.range c, if j ≤ k then f j else 0) =
      ∑ j ∈ Finset.range (k + 1), if j < c then f j else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem count_succ_explicit (n k : ℕ) (r : ZMod (3 ^ (n + 1))) :
    count (n + 1) k r = ∑ j ∈ Finset.range (k + 1),
      if j < period n then
        let s : ZMod (3 ^ (n + 1)) := 2 ^ (j + 1) * r
        if s.val % 3 = 1 then count n (k - j) ((s.val / 3 : ℕ) : ZMod (3 ^ n)) else 0
      else 0 := by
  unfold count
  rw [generator]
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow_mul']
  simp only [polynomialBoundary_explicit]
  have hcoeff (p : Prop) [Decidable p] (q : Polynomial ℕ) (d : ℕ) :
      (if p then q else 0).coeff d = if p then q.coeff d else 0 := by
    split_ifs <;> simp
  simp only [hcoeff]
  exact sum_range_cutoff _ _ _

/-- A computable inverse recursion, proved equal to the polynomial coefficient.
The cost bound prevents traversing an entire exponentially large period. -/
def recursiveCount : (n : ℕ) → ℕ → ZMod (3 ^ n) → ℕ
  | 0, k, _ => if k = 0 then 1 else 0
  | n + 1, k, r => ∑ j ∈ Finset.range (k + 1),
      if j < period n then
        let s : ZMod (3 ^ (n + 1)) := 2 ^ (j + 1) * r
        if s.val % 3 = 1 then recursiveCount n (k - j) ((s.val / 3 : ℕ) : ZMod (3 ^ n)) else 0
      else 0

theorem recursiveCount_eq_count (n : ℕ) :
    ∀ k : ℕ, ∀ r : ZMod (3 ^ n), recursiveCount n k r = count n k r := by
  induction n with
  | zero => intro k r; simpa [recursiveCount] using (count_zero k r).symm
  | succ n ih =>
    intro k r
    simp only [recursiveCount, count_succ_explicit]
    simp_rw [ih]

theorem count_two_two_four : count 2 2 4 = 0 := by
  rw [← recursiveCount_eq_count]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem count_twelve_twelve_seven : count 12 12 7 = 0 := by
  rw [← recursiveCount_eq_count]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem count_twelve_twelve_one_pos : 0 < count 12 12 1 := by
  rw [← recursiveCount_eq_count]
  decide

theorem value_pos_of_unit {n : ℕ} (hn : 1 ≤ n) {r : ZMod (3 ^ n)} (hr : IsUnit r) :
    0 < value n r := by
  obtain ⟨c, hc, h⟩ := uniform_generator_value_lower
  exact (mul_pos hc (by positivity)).trans_le (h n hn r hr)

/-- A certified distinction between a positive marginal and a zero
central-cost coefficient. This finite depth does not refute an eventual
coefficient estimate with an unspecified onset. -/
theorem central_zero_with_positive_value :
    count 12 12 7 = 0 ∧ 0 < count 12 12 1 ∧ 0 < value 12 7 := by
  refine ⟨count_twelve_twelve_seven, count_twelve_twelve_one_pos, ?_⟩
  apply value_pos_of_unit (by norm_num)
  exact (ZMod.isUnit_iff_coprime 7 (3 ^ 12)).mpr (by decide)

end
end CollatzTargetDensity.FixedCostGenerators
