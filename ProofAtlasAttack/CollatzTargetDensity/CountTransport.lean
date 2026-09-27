import Erdos1135.Terras.Density.NaturalDensity
import Mathlib.Data.Finset.Prod

/-! Finite-fibre transport of positive lower natural density. -/
namespace CollatzTargetDensity
open Erdos1135
noncomputable section

def HasPositiveLowerDensity (A : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    c * (X : ℝ) ≤ (Terras.natCount A X : ℝ)

/-- An injective encoding by a bounded label and an output gives a counting
bound, even when the output map itself is not injective. -/
theorem count_le_of_labelled_injection (A B : Set ℕ) (Q K : ℕ)
    (label output : ℕ → ℕ) (hinj : Function.Injective (fun n => (label n, output n)))
    (hlabel : ∀ n, label n < Q)
    (hmem : ∀ n ∈ A, output n ∈ B)
    (hsize : ∀ n X, n < X → output n < K * X) (X : ℕ) :
    Terras.natCount A X ≤ Q * Terras.natCount B (K * X) := by
  classical
  let s := (Finset.range X).filter (fun n => n ∈ A)
  let u := (Finset.range (K * X)).filter (fun n => n ∈ B)
  let v : Finset (ℕ × ℕ) := (Finset.range Q) ×ˢ u
  have hm : Set.MapsTo (fun n => (label n, output n)) s v := by
    intro n hn
    obtain ⟨hnlt, hnA⟩ := Finset.mem_filter.mp hn
    change (label n, output n) ∈ (Finset.range Q) ×ˢ u
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hlabel n),
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (hsize n X (Finset.mem_range.mp hnlt)), hmem n hnA⟩⟩
  have hc := Finset.card_le_card_of_injOn _ hm hinj.injOn
  simpa only [s, u, v, Finset.card_product, Finset.card_range, Terras.natCount,
    Nat.count_eq_card_filter_range] using hc

/-- A uniform count comparison at dilated cutoffs transfers lower density.
The explicit loss is at most `2*K*Q`. -/
theorem positive_density_of_count_transport {A B : Set ℕ} {Q K : ℕ}
    (hQ : 0 < Q) (hK : 0 < K)
    (hcount : ∀ X, Terras.natCount A X ≤ Q * Terras.natCount B (K * X))
    (hA : HasPositiveLowerDensity A) : HasPositiveLowerDensity B := by
  classical
  obtain ⟨c, hc, X₀, hX₀⟩ := hA
  refine ⟨c / (2 * (K : ℝ) * Q), by positivity, max (K * X₀) (2 * K), ?_⟩
  intro X hX
  have hlarge : K * X₀ ≤ X := (le_max_left _ _).trans hX
  have htwice : 2 * K ≤ X := (le_max_right _ _).trans hX
  have hdiv : X₀ ≤ X / K := (Nat.le_div_iff_mul_le hK).2 (by simpa [Nat.mul_comm] using hlarge)
  have hround : X ≤ 2 * K * (X / K) := by
    have hrem := Nat.mod_lt X hK
    have hdecomp := Nat.mod_add_div X K
    have hq : 1 ≤ X / K := (Nat.le_div_iff_mul_le hK).2 (by omega)
    have hm := Nat.mul_le_mul_left K hq
    nlinarith
  have hmono : Terras.natCount B (K * (X / K)) ≤ Terras.natCount B X := by
    unfold Terras.natCount
    exact Nat.count_monotone _ (Nat.mul_div_le X K)
  have hbound : Terras.natCount A (X / K) ≤ Q * Terras.natCount B X :=
    (hcount (X / K)).trans (Nat.mul_le_mul_left Q hmono)
  have ha := hX₀ (X / K) hdiv
  have hb : (Terras.natCount A (X / K) : ℝ) ≤
      (Q : ℝ) * Terras.natCount B X := by exact_mod_cast hbound
  have hr : (X : ℝ) ≤ 2 * (K : ℝ) * (X / K : ℕ) := by exact_mod_cast hround
  have hkr : (0 : ℝ) < K := by exact_mod_cast hK
  have hqr : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show (0 : ℝ) < 2 * K * Q by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_left hr hc.le,
    mul_le_mul_of_nonneg_left (ha.trans hb) (show (0 : ℝ) ≤ 2 * K by positivity)]

/-- Discarding a fixed initial interval preserves positive lower density. -/
theorem positive_density_tail {A : Set ℕ} (hA : HasPositiveLowerDensity A) (R : ℕ) :
    HasPositiveLowerDensity {n | n ∈ A ∧ R ≤ n} := by
  classical
  obtain ⟨c, hc, X₀, hX₀⟩ := hA
  obtain ⟨Y, hY⟩ := exists_nat_gt (2 * (R : ℝ) / c)
  refine ⟨c / 2, by positivity, max X₀ Y, ?_⟩
  intro X hX
  have hcount : Terras.natCount A X ≤ R +
      Terras.natCount {n | n ∈ A ∧ R ≤ n} X := by
    have hsub : (Finset.range X).filter (fun n => n ∈ A) ⊆
        Finset.range R ∪ (Finset.range X).filter (fun n => n ∈ A ∧ R ≤ n) := by
      intro n hn
      obtain ⟨hnX, hnA⟩ := Finset.mem_filter.mp hn
      by_cases h : n < R
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnX, hnA, by omega⟩)
    have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simp only [Finset.card_range] at h
    unfold Terras.natCount
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    convert h using 1
    congr 2
    ext x
    simp only [Finset.mem_filter, Set.mem_setOf_eq]
  have hreal : (Terras.natCount A X : ℝ) ≤ (R : ℝ) +
      Terras.natCount {n | n ∈ A ∧ R ≤ n} X := by exact_mod_cast hcount
  have hXY : (Y : ℝ) ≤ X := by exact_mod_cast (le_max_right _ _).trans hX
  have hpaid := (div_lt_iff₀ hc).mp hY
  have ha := hX₀ X ((le_max_left _ _).trans hX)
  nlinarith

theorem count_le_of_injection_on (A B : Set ℕ) (K : ℕ) (f : ℕ → ℕ)
    (hinj : A.InjOn f) (hmem : ∀ n ∈ A, f n ∈ B)
    (hsize : ∀ n ∈ A, ∀ X, n < X → f n < K * X) (X : ℕ) :
    Terras.natCount A X ≤ Terras.natCount B (K * X) := by
  classical
  have hm : Set.MapsTo f ((Finset.range X).filter (fun n => n ∈ A))
      ((Finset.range (K * X)).filter (fun n => n ∈ B)) := by
    intro n hn
    obtain ⟨hnX, hnA⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (hsize n hnA X (Finset.mem_range.mp hnX)), hmem n hnA⟩
  have hi : Set.InjOn f ((Finset.range X).filter (fun n => n ∈ A)) :=
    fun n hn m hm he => hinj (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hm).2 he
  simpa only [Terras.natCount, Nat.count_eq_card_filter_range] using
    Finset.card_le_card_of_injOn f hm hi

end
end CollatzTargetDensity
