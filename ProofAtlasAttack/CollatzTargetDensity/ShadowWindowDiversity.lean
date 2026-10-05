import CollatzTargetDensity.ShadowGridCore
import CollatzTargetDensity.ShadowReturnArithmetic

/-!
Finite near-return arithmetic forces diversity in compatible Collatz shadows.
The statements concern the explicit integer and real recurrences below; they
neither assert existence of a divergent Collatz orbit nor prove convergence.
-/
namespace CollatzTargetDensity.ShadowWindowDiversity
open ShadowGridCore ShadowReturnArithmetic
noncomputable section

def gridDenominator (r : ℕ) : ℕ := (3 ^ r).factorial

def tolerance (C r : ℕ) (M : ℝ) : ℝ :=
  1 / (12 * (gridDenominator r : ℝ) * (C : ℝ) ^ r * (M + 1))

theorem gridDenominator_pos (r : ℕ) : 0 < gridDenominator r :=
  Nat.factorial_pos _

theorem tolerance_bounds {C r : ℕ} {M : ℝ} (hC : 1 ≤ C) (hM : 1 ≤ M) :
    0 < tolerance C r M ∧
    (C : ℝ) ^ r * tolerance C r M < 1 ∧
    (gridDenominator r : ℝ) * (C : ℝ) ^ r * tolerance C r M <
      1 / (6 * (M + 1)) := by
  have hQ : (0 : ℝ) < gridDenominator r := by exact_mod_cast gridDenominator_pos r
  have hQone : (1 : ℝ) ≤ gridDenominator r := by exact_mod_cast gridDenominator_pos r
  have hCr : (0 : ℝ) < (C : ℝ) ^ r := by positivity
  have hMp : 0 < M + 1 := by linarith
  have hpos : 0 < tolerance C r M := by unfold tolerance; positivity
  have heq : (gridDenominator r : ℝ) * (C : ℝ) ^ r * tolerance C r M =
      1 / (12 * (M + 1)) := by
    unfold tolerance
    field_simp
  have hs : (1 / (12 * (M + 1)) : ℝ) < 1 / (6 * (M + 1)) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have ht : (1 / (6 * (M + 1)) : ℝ) < 1 := by
    apply (div_lt_iff₀ (by positivity)).2
    linarith
  have hmul := mul_le_mul_of_nonneg_right hQone
    (mul_nonneg hCr.le hpos.le)
  refine ⟨hpos, ?_, ?_⟩
  · have heq' := heq
    nlinarith
  · rw [heq]
    exact hs

/-- All possible short-return denominators divide a single explicit integer. -/
theorem lift_anchor_to_grid {r C q m : ℕ} {z η : ℝ}
    (hq : 0 < q) (hqr : q ≤ 3 ^ r) (hη : 0 ≤ η)
    (herror : |(q : ℝ) * z - (m : ℝ)| ≤ (C : ℝ) ^ r * η) :
    ∃ b : ℕ, |(gridDenominator r : ℝ) * z - (b : ℝ)| ≤
      (gridDenominator r : ℝ) * (C : ℝ) ^ r * η := by
  have hdiv : q ∣ gridDenominator r := Nat.dvd_factorial hq hqr
  let d : ℕ := gridDenominator r / q
  have hd : d * q = gridDenominator r := Nat.div_mul_cancel hdiv
  have hdle : d ≤ gridDenominator r := Nat.div_le_self _ _
  have hdR : (d : ℝ) * (q : ℝ) = gridDenominator r := by exact_mod_cast hd
  have hbound := mul_le_mul_of_nonneg_left herror (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hbound' := mul_le_mul_of_nonneg_right
    (show (d : ℝ) ≤ gridDenominator r by exact_mod_cast hdle)
    (mul_nonneg (by positivity : (0 : ℝ) ≤ (C : ℝ) ^ r) hη)
  refine ⟨d * m, ?_⟩
  have hid : (gridDenominator r : ℝ) * z - ((d * m : ℕ) : ℝ) =
      (d : ℝ) * ((q : ℝ) * z - (m : ℝ)) := by
    push_cast
    rw [← hdR]
    ring
  rw [hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
  nlinarith

/-- If every short window has a close pair, the entire trace has a finite
length barrier. This is a finite theorem about the actual 3x+1 recurrence
and a compatible real correction. -/
theorem window_collapse_barrier (L r C : ℕ) (a x : ℕ → ℕ) (E : ℕ → ℝ)
    (hx0 : 0 < x 0) {M : ℝ} (hM : 1 ≤ M) (hC : 1 ≤ C)
    (hCM : 3 * M ≤ (C : ℝ))
    (ha : ∀ i < L + r, 1 ≤ a i)
    (hplus : ∀ i < L + r, 2 ^ a i * x (i + 1) = 3 * x i + 1)
    (hminus : ∀ i < L + r, (2 : ℝ) ^ a i * E (i + 1) = 3 * E i - 1)
    (hlow : ∀ i ≤ L + r, 1 ≤ E i) (hupp : ∀ i ≤ L + r, E i ≤ M)
    (hpairs : ∀ i ≤ L, ∃ j p : ℕ, 0 < p ∧ j + p ≤ r ∧
      |E (i + (j + p)) - E (i + j)| ≤ tolerance C r M) :
    (2 : ℝ) ^ L < (gridDenominator r : ℝ) * ((x 0 : ℝ) + M) + 1 := by
  obtain ⟨hη, hsmall, hgrid⟩ := tolerance_bounds (r := r) hC hM
  have hc (i : ℕ) (hi : i < L + r) : 1 ≤ 2 ^ a i ∧ 2 ^ a i ≤ C := by
    refine ⟨Nat.pow_pos (by decide), ?_⟩
    have hl := hlow (i + 1) (by omega)
    have hu := hupp i (by omega)
    have hs := hminus i hi
    have hp : (0 : ℝ) ≤ 2 ^ a i := by positivity
    have hh := mul_le_mul_of_nonneg_left hl hp
    have hr : (2 : ℝ) ^ a i ≤ C := by nlinarith
    exact_mod_cast hr
  have happrox (i : ℕ) (hi : i ≤ L) : ∃ b : ℕ,
      |(gridDenominator r : ℝ) * E i - (b : ℝ)| < 1 / (6 * (M + 1)) := by
    obtain ⟨j, p, hp, hjp, hclose⟩ := hpairs i hi
    obtain ⟨q, m, hq, hqr, herr⟩ := near_return_integer_anchor
      (fun k => E (i + k)) (fun k => 2 ^ a (i + k)) r j p C hp hjp hC
      (fun k hk => hc (i + k) (by omega))
      (fun k hk => by
        simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.add_assoc] using
          hminus (i + k) (by omega))
      (hlow (i + j) (by omega)) hη.le hsmall hclose
    simp only [Nat.add_zero] at herr
    obtain ⟨b, hb⟩ := lift_anchor_to_grid hq hqr hη.le herr
    exact ⟨b, hb.trans_lt hgrid⟩
  have hchoose : ∀ i : ℕ, ∃ b : ℕ, i ≤ L →
      |(gridDenominator r : ℝ) * E i - (b : ℝ)| < 1 / (6 * (M + 1)) := by
    intro i
    by_cases hi : i ≤ L
    · obtain ⟨b, hb⟩ := happrox i hi
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => False.elim (hi h)⟩
  choose b hb using hchoose
  exact finite_grid_barrier L a x b E (gridDenominator_pos r) hx0 hM
    (fun i hi => ha i (by omega)) (fun i hi => hplus i (by omega))
    (fun i hi => hminus i (by omega)) (fun i hi => hlow i (by omega))
    (fun i hi => hupp i (by omega)) hb

/-- Long enough traces contain a consecutive window whose correction values
are pairwise separated by an explicit positive tolerance. -/
theorem finite_separated_window (L r C : ℕ) (a x : ℕ → ℕ) (E : ℕ → ℝ)
    (hx0 : 0 < x 0) {M : ℝ} (hM : 1 ≤ M) (hC : 1 ≤ C)
    (hCM : 3 * M ≤ (C : ℝ))
    (ha : ∀ i < L + r, 1 ≤ a i)
    (hplus : ∀ i < L + r, 2 ^ a i * x (i + 1) = 3 * x i + 1)
    (hminus : ∀ i < L + r, (2 : ℝ) ^ a i * E (i + 1) = 3 * E i - 1)
    (hlow : ∀ i ≤ L + r, 1 ≤ E i) (hupp : ∀ i ≤ L + r, E i ≤ M)
    (hlength : (gridDenominator r : ℝ) * ((x 0 : ℝ) + M) + 1 ≤ (2 : ℝ) ^ L) :
    ∃ i ≤ L, ∀ j k : ℕ, j < k → k ≤ r →
      tolerance C r M < |E (i + k) - E (i + j)| := by
  by_contra! h
  have hpairs : ∀ i ≤ L, ∃ j p : ℕ, 0 < p ∧ j + p ≤ r ∧
      |E (i + (j + p)) - E (i + j)| ≤ tolerance C r M := by
    intro i hi
    obtain ⟨j, k, hjk, hkr, hclose⟩ := h i hi
    refine ⟨j, k - j, by omega, by omega, ?_⟩
    simpa only [Nat.add_sub_of_le hjk.le] using hclose
  have hb := window_collapse_barrier L r C a x E hx0 hM hC hCM
    ha hplus hminus hlow hupp hpairs
  exact (not_lt_of_ge hlength) hb

end
end CollatzTargetDensity.ShadowWindowDiversity
