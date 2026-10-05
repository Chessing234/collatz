import Collatz.Strategy.AccumulatorCap
import Init.Data.Rat.Lemmas

/-!
Finite rational certificates for the inverse-sign Syracuse recurrence.
The certificate identifies a finite integer trajectory; it neither supplies
the certificate from a starting integer nor establishes eventual descent.
-/
namespace Collatz.ShadowDecoder

/-- A rational sample pair, with residual strictly less than one half. -/
def Fits (c : Nat) (u v : Rat) : Prop :=
  1 ≤ v ∧ -1 < 2 * ((c : Rat) * v - 3 * u + 1) ∧
    2 * ((c : Rat) * v - 3 * u + 1) < 1

/-- Integer coefficients can be recovered despite a small residual. -/
theorem fits_unique {c d : Nat} {u v : Rat}
    (hc : Fits c u v) (hd : Fits d u v) : c = d := by
  have rule {c d : Nat} (hc : Fits c u v) (hd : Fits d u v) : ¬ c < d := by
    intro h
    have hcast : ((c + 1 : Nat) : Rat) ≤ (d : Rat) :=
      Rat.natCast_le_natCast.mpr h
    have hv : 0 ≤ v := by have := hc.1; grind
    have hp := Rat.mul_le_mul_of_nonneg_right hcast hv
    rcases hc with ⟨hcv, hc0, hc1⟩
    rcases hd with ⟨hdv, hd0, hd1⟩
    grind
  have h₁ := rule hc hd
  have h₂ := rule hd hc
  omega

/-- Even division coefficients permit twice the residual tolerance. -/
def EvenFits (c : Nat) (u v : Rat) : Prop :=
  1 ≤ v ∧ -1 < (c : Rat) * v - 3 * u + 1 ∧
    (c : Rat) * v - 3 * u + 1 < 1

theorem evenFits_unique {c d : Nat} {u v : Rat}
    (hc2 : 2 ∣ c) (hd2 : 2 ∣ d)
    (hc : EvenFits c u v) (hd : EvenFits d u v) : c = d := by
  have rule {c d : Nat} (hc2 : 2 ∣ c) (hd2 : 2 ∣ d)
      (hc : EvenFits c u v) (hd : EvenFits d u v) : ¬ c < d := by
    intro h
    have hgap : c + 2 ≤ d := by
      obtain ⟨a, ha⟩ := hc2
      obtain ⟨b, hb⟩ := hd2
      omega
    have hcast := Rat.natCast_le_natCast.mpr hgap
    have hv : 0 ≤ v := by have := hc.1; grind
    have hp := Rat.mul_le_mul_of_nonneg_right hcast hv
    rcases hc with ⟨hcv, hc0, hc1⟩
    rcases hd with ⟨hdv, hd0, hd1⟩
    grind
  have h₁ := rule hc2 hd2 hc hd
  have h₂ := rule hd2 hc2 hd hc
  omega

/-- A directly checkable precision budget converts sample errors into a
valid residual certificate. Samples must preserve the lower bound one. -/
theorem approximation_fits {c : Nat} {u v s t δ : Rat}
    (hexact : (c : Rat) * v - 3 * u + 1 = 0)
    (ht : 1 ≤ t)
    (hslo : -δ ≤ s - u) (hshi : s - u ≤ δ)
    (htlo : -δ ≤ t - v) (hthi : t - v ≤ δ)
    (hbudget : ((c : Rat) + 3) * δ < 1) : EvenFits c s t := by
  have hc : (0 : Rat) ≤ (c : Rat) := Rat.natCast_le_natCast.mpr (Nat.zero_le c)
  have hlo := Rat.mul_le_mul_of_nonneg_left htlo hc
  have hhi := Rat.mul_le_mul_of_nonneg_left hthi hc
  unfold EvenFits
  grind

/-- The strict residual bound one is optimal, even for powers of two:
the closed bound one admits both coefficients 2 and 4. -/
theorem closed_tolerance_ambiguous :
    (2 : Rat) * 1 - 3 * (4 / 3) + 1 = -1 ∧
    (4 : Rat) * 1 - 3 * (4 / 3) + 1 = 1 := by grind

/-- Backward construction with terminal shadow one. -/
def encode : Nat → (Nat → Nat) → Nat → Rat
  | 0, _, _ => 1
  | L + 1, c, 0 => ((c 0 : Rat) * encode L (fun i => c (i + 1)) 0 + 1) / 3
  | L + 1, c, i + 1 => encode L (fun j => c (j + 1)) i

theorem encode_ge_one (L : Nat) (c : Nat → Nat)
    (hc : ∀ i < L, 2 ≤ c i) (i : Nat) : 1 ≤ encode L c i := by
  induction L generalizing c i with
  | zero => simp [encode]
  | succ L ih =>
    have ht := ih (fun j => c (j + 1)) (fun j hj => hc (j + 1) (by omega))
    cases i with
    | zero =>
      have h := ht 0
      have hcR : (2 : Rat) ≤ (c 0 : Rat) := Rat.natCast_le_natCast.mpr (hc 0 (by omega))
      have hp := Rat.mul_le_mul_of_nonneg_right hcR (show 0 ≤ encode L (fun j => c (j + 1)) 0 by grind)
      simp only [encode]
      grind
    | succ i => exact ht i

theorem encode_exact (L : Nat) (c : Nat → Nat) (i : Nat) (hi : i < L) :
    (c i : Rat) * encode L c (i + 1) - 3 * encode L c i + 1 = 0 := by
  induction L generalizing c i with
  | zero => omega
  | succ L ih =>
    cases i with
    | zero => simp only [encode]; grind
    | succ i => exact ih (fun j => c (j + 1)) i (by omega)

/-- Every finite coefficient word >= 2 has an exact certificate. Therefore
finite certificate existence alone imposes no stopping-time restriction. -/
theorem encode_fits (L : Nat) (c : Nat → Nat)
    (hc : ∀ i < L, 2 ≤ c i) (i : Nat) (hi : i < L) :
    EvenFits (c i) (encode L c i) (encode L c (i + 1)) := by
  have hl := encode_ge_one L c hc (i + 1)
  have he := encode_exact L c i hi
  unfold EvenFits
  grind

private theorem two_pow_mod_three_ne (k : Nat) : 2 ^ k % 3 ≠ 0 := by
  have h : ∀ k : Nat, 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih => rw [Nat.pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> decide
  have := h k
  omega

/-- Every even coefficient in a common block contributes one binary digit. -/
theorem even_block_dvd (L : Nat) (c b : Nat → Nat)
    (heven : ∀ i < L, 2 ∣ c i)
    (hstep : ∀ i < L, c i * b (i + 1) = 3 * b i) : 2 ^ L ∣ b 0 := by
  induction L generalizing c b with
  | zero => simp
  | succ L ih =>
    have ht := ih (fun i => c (i + 1)) (fun i => b (i + 1))
      (fun i hi => heven (i + 1) (by omega))
      (fun i hi => hstep (i + 1) (by omega))
    have hm := Nat.mul_dvd_mul ht (heven 0 (by omega))
    rw [← Nat.pow_succ, Nat.mul_comm (b 1), hstep 0 (by omega)] at hm
    exact AccumulatorCap.dvd_cancel_three (two_pow_mod_three_ne _) hm

/-- A shared certificate forces both directed start differences to be
divisible by 2^L. No periodicity or infinite-orbit premise is needed. -/
theorem certificate_dvd (L : Nat) (x y c d : Nat → Nat) (s : Nat → Rat)
    (hc : ∀ i < L, 2 ∣ c i) (hd : ∀ i < L, 2 ∣ d i)
    (hx : ∀ i < L, c i * x (i + 1) = 3 * x i + 1)
    (hy : ∀ i < L, d i * y (i + 1) = 3 * y i + 1)
    (hcx : ∀ i < L, EvenFits (c i) (s i) (s (i + 1)))
    (hdy : ∀ i < L, EvenFits (d i) (s i) (s (i + 1))) :
    2 ^ L ∣ y 0 - x 0 := by
  have heq (i : Nat) (hi : i < L) : c i = d i :=
    evenFits_unique (hc i hi) (hd i hi) (hcx i hi) (hdy i hi)
  apply even_block_dvd L c (fun i => y i - x i) hc
  intro i hi
  rw [Nat.mul_sub, hx i hi, heq i hi, hy i hi]
  omega

/-- A finite noisy shadow certificate uniquely identifies its starting
integer inside any interval of diameter less than 2^L. -/
theorem certificate_unique (L : Nat) (x y c d : Nat → Nat) (s : Nat → Rat)
    (hc : ∀ i < L, 2 ∣ c i) (hd : ∀ i < L, 2 ∣ d i)
    (hx : ∀ i < L, c i * x (i + 1) = 3 * x i + 1)
    (hy : ∀ i < L, d i * y (i + 1) = 3 * y i + 1)
    (hcx : ∀ i < L, EvenFits (c i) (s i) (s (i + 1)))
    (hdy : ∀ i < L, EvenFits (d i) (s i) (s (i + 1)))
    (hxy : x 0 - y 0 < 2 ^ L) (hyx : y 0 - x 0 < 2 ^ L) : x 0 = y 0 := by
  have h₁ := certificate_dvd L x y c d s hc hd hx hy hcx hdy
  have h₂ := certificate_dvd L y x d c s hd hc hy hx hdy hcx
  have hz₁ : y 0 - x 0 = 0 := by
    by_cases h : y 0 - x 0 = 0
    · exact h
    · have := Nat.le_of_dvd (by omega : 0 < y 0 - x 0) h₁
      omega
  have hz₂ : x 0 - y 0 = 0 := by
    by_cases h : x 0 - y 0 = 0
    · exact h
    · have := Nat.le_of_dvd (by omega : 0 < x 0 - y 0) h₂
      omega
  omega

end Collatz.ShadowDecoder
