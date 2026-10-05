import CollatzTargetDensity.ShadowWindowDiversity

/-!
# Quantization obstruction for bounded compatible shadows

The finite separated-window device applies on every tail of an infinite
integer `3x+1` trace with a bounded compatible real correction. Consequently
no fixed finite set of real levels can approximate all sufficiently late
corrections at the explicit radius below. The levels need not be rational.

All hypotheses are displayed. These statements do not assert the existence
of an infinite divergent Collatz trace, nor do they prove its impossibility.
-/

namespace CollatzTargetDensity.ShadowQuantization

open ShadowWindowDiversity

noncomputable section

/-- A finite compatible trace staying within a fixed dictionary of `r` real
levels cannot exceed the explicit exponential length barrier. The dictionary
entries may be irrational and its labels may vary arbitrarily in time. -/
theorem finite_dictionary_barrier (L r C : ℕ) (a x : ℕ → ℕ) (E : ℕ → ℝ)
    (hx0 : 0 < x 0) {M : ℝ} (hM : 1 ≤ M) (hC : 1 ≤ C)
    (hCM : 3 * M ≤ (C : ℝ))
    (ha : ∀ i < L + r, 1 ≤ a i)
    (hplus : ∀ i < L + r, 2 ^ a i * x (i + 1) = 3 * x i + 1)
    (hminus : ∀ i < L + r, (2 : ℝ) ^ a i * E (i + 1) = 3 * E i - 1)
    (hlow : ∀ i ≤ L + r, 1 ≤ E i) (hupp : ∀ i ≤ L + r, E i ≤ M)
    (F : Fin r → ℝ) (labels : ℕ → Fin r)
    (happrox : ∀ i ≤ L + r,
      |E i - F (labels i)| ≤ tolerance C r M / 2) :
    (2 : ℝ) ^ L < (gridDenominator r : ℝ) * ((x 0 : ℝ) + M) + 1 := by
  classical
  by_contra! hlength
  obtain ⟨i, hi, hsep⟩ := finite_separated_window L r C a x E hx0 hM hC hCM
    ha hplus hminus hlow hupp hlength
  let f (j : Fin (r + 1)) : Fin r := labels (i + j.val)
  have hcollision (u v : Fin (r + 1)) (huv : u.val < v.val)
      (heq : f u = f v) : False := by
    have hs := hsep u.val v.val huv (by omega)
    have hu := happrox (i + u.val) (by omega)
    have hv := happrox (i + v.val) (by omega)
    change labels (i + u.val) = labels (i + v.val) at heq
    have hdist : |E (i + v.val) - E (i + u.val)| ≤
        |E (i + v.val) - F (labels (i + v.val))| +
          |F (labels (i + v.val)) - E (i + u.val)| := abs_sub_le _ _ _
    rw [← heq, abs_sub_comm (F (labels (i + u.val))) (E (i + u.val))] at hdist
    rw [← heq] at hv
    linarith
  have hinj : Function.Injective f := by
    intro u v heq
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hcollision u v hlt heq
    · exact hcollision v u hgt heq.symm
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- Every tail has a consecutive block of `r+1` pairwise separated correction
values. The separation is uniform over the starting time of the tail. -/
theorem arbitrarily_late_separated_windows (a x : ℕ → ℕ) (E : ℕ → ℝ)
    (hx : ∀ i, 0 < x i) {M : ℝ} (hM : 1 ≤ M) (C : ℕ) (hC : 1 ≤ C)
    (hCM : 3 * M ≤ (C : ℝ))
    (ha : ∀ i, 1 ≤ a i)
    (hplus : ∀ i, 2 ^ a i * x (i + 1) = 3 * x i + 1)
    (hminus : ∀ i, (2 : ℝ) ^ a i * E (i + 1) = 3 * E i - 1)
    (hlow : ∀ i, 1 ≤ E i) (hupp : ∀ i, E i ≤ M) (r N : ℕ) :
    ∃ i ≥ N, ∀ j k : ℕ, j < k → k ≤ r →
      tolerance C r M < |E (i + k) - E (i + j)| := by
  obtain ⟨L, hL⟩ := exists_nat_gt
    ((gridDenominator r : ℝ) * ((x N : ℝ) + M) + 1)
  have hpow : (L : ℝ) < (2 : ℝ) ^ L := by
    exact_mod_cast (Nat.lt_two_pow_self (n := L))
  have hlength : (gridDenominator r : ℝ) * ((x N : ℝ) + M) + 1 ≤
      (2 : ℝ) ^ L := hL.le.trans hpow.le
  obtain ⟨i, hi, hsep⟩ := finite_separated_window L r C
    (fun k => a (N + k)) (fun k => x (N + k)) (fun k => E (N + k))
    (by simpa using hx N) hM hC hCM
    (fun k _ => ha (N + k))
    (fun k _ => by simpa only [Nat.add_assoc] using hplus (N + k))
    (fun k _ => by simpa only [Nat.add_assoc] using hminus (N + k))
    (fun k _ => hlow (N + k)) (fun k _ => hupp (N + k))
    (by simpa using hlength)
  refine ⟨N + i, by omega, ?_⟩
  intro j k hjk hkr
  simpa only [Nat.add_assoc] using hsep j k hjk hkr

/-- Every fixed finite collection of arbitrary real levels is escaped by a
uniform positive margin on every tail. With `s` levels the margin is half
the tolerance for a window of `s+1` points. -/
theorem finite_alphabet_exclusion (a x : ℕ → ℕ) (E : ℕ → ℝ)
    (hx : ∀ i, 0 < x i) {M : ℝ} (hM : 1 ≤ M) (C : ℕ) (hC : 1 ≤ C)
    (hCM : 3 * M ≤ (C : ℝ))
    (ha : ∀ i, 1 ≤ a i)
    (hplus : ∀ i, 2 ^ a i * x (i + 1) = 3 * x i + 1)
    (hminus : ∀ i, (2 : ℝ) ^ a i * E (i + 1) = 3 * E i - 1)
    (hlow : ∀ i, 1 ≤ E i) (hupp : ∀ i, E i ≤ M)
    (s : ℕ) (F : Fin s → ℝ) (N : ℕ) :
    ∃ k ≥ N, ∀ f : Fin s, tolerance C s M / 2 < |E k - F f| := by
  classical
  by_contra! h
  obtain ⟨i, hi, hsep⟩ := arbitrarily_late_separated_windows
    a x E hx hM C hC hCM ha hplus hminus hlow hupp s N
  have hlevels : ∀ j : Fin (s + 1), ∃ f : Fin s,
      |E (i + j.val) - F f| ≤ tolerance C s M / 2 := by
    intro j
    exact h (i + j.val) (by omega)
  choose labels hlabels using hlevels
  have hcollision (u v : Fin (s + 1)) (huv : u.val < v.val)
      (heq : labels u = labels v) : False := by
    have hs := hsep u.val v.val huv (by omega)
    have hu := hlabels u
    have hv := hlabels v
    have hdist : |E (i + v.val) - E (i + u.val)| ≤
        |E (i + v.val) - F (labels v)| + |F (labels v) - E (i + u.val)| :=
      abs_sub_le _ _ _
    rw [← heq, abs_sub_comm (F (labels u)) (E (i + u.val))] at hdist
    rw [← heq] at hv
    linarith
  have hinj : Function.Injective labels := by
    intro u v heq
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hcollision u v hlt heq
    · exact hcollision v u hgt heq.symm
  have hcard := Fintype.card_le_of_injective labels hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- Without assuming the correction is bounded, every fixed finite real
alphabet is escaped by a positive margin arbitrarily late. If the correction
is eventually bounded, the quantitative dictionary theorem applies; otherwise
large correction values themselves escape every member of the alphabet. -/
theorem finite_alphabet_escape (a x : ℕ → ℕ) (E : ℕ → ℝ)
    (hx : ∀ i, 0 < x i)
    (ha : ∀ i, 1 ≤ a i)
    (hplus : ∀ i, 2 ^ a i * x (i + 1) = 3 * x i + 1)
    (hminus : ∀ i, (2 : ℝ) ^ a i * E (i + 1) = 3 * E i - 1)
    (hlow : ∀ i, 1 ≤ E i) (s : ℕ) (F : Fin s → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ k ≥ N, ∀ f : Fin s, ε < |E k - F f| := by
  classical
  let M : ℝ := 1 + ∑ f : Fin s, |F f|
  have hM : 1 ≤ M := by
    have hsum : (0 : ℝ) ≤ ∑ f : Fin s, |F f| :=
      Finset.sum_nonneg (fun f _ => abs_nonneg (F f))
    dsimp [M]
    linarith
  have hF (f : Fin s) : F f + 1 ≤ M := by
    have hf : |F f| ≤ ∑ g : Fin s, |F g| :=
      Finset.single_le_sum (fun g _ => abs_nonneg (F g)) (Finset.mem_univ f)
    have hfa := le_abs_self (F f)
    dsimp [M]
    linarith
  obtain ⟨C, hCstrict⟩ := exists_nat_gt (3 * M)
  have hCpos : 0 < C := by
    exact_mod_cast (show (0 : ℝ) < (C : ℝ) by linarith)
  have hC : 1 ≤ C := hCpos
  have hCM : 3 * M ≤ (C : ℝ) := hCstrict.le
  let ε : ℝ := min (1 / 2) (tolerance C s M / 2)
  have hεpos : 0 < ε := by
    have ht := (tolerance_bounds (r := s) hC hM).1
    exact lt_min (by norm_num) (half_pos ht)
  have hεsmall : ε ≤ 1 / 2 := min_le_left _ _
  have hεtol : ε ≤ tolerance C s M / 2 := min_le_right _ _
  refine ⟨ε, hεpos, ?_⟩
  by_cases hbounded : ∃ N₀ : ℕ, ∀ k ≥ N₀, E k ≤ M
  · obtain ⟨N₀, hbound⟩ := hbounded
    intro N
    obtain ⟨k, hk, hfar⟩ := finite_alphabet_exclusion
      (fun i => a (N₀ + i)) (fun i => x (N₀ + i)) (fun i => E (N₀ + i))
      (fun i => hx (N₀ + i)) hM C hC hCM (fun i => ha (N₀ + i))
      (fun i => by simpa only [Nat.add_assoc] using hplus (N₀ + i))
      (fun i => by simpa only [Nat.add_assoc] using hminus (N₀ + i))
      (fun i => hlow (N₀ + i)) (fun i => hbound (N₀ + i) (by omega)) s F N
    refine ⟨N₀ + k, by omega, ?_⟩
    intro f
    exact hεtol.trans_lt (hfar f)
  · push Not at hbounded
    intro N
    obtain ⟨k, hk, hlarge⟩ := hbounded N
    refine ⟨k, hk, ?_⟩
    intro f
    have hf := hF f
    have hab := le_abs_self (E k - F f)
    linarith

end
end CollatzTargetDensity.ShadowQuantization
