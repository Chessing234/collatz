import Collatz.Strategy.ShadowTerminal

/-! Selecting a suffix with no coefficient crossing. The eventual multiplier
bound is an explicit hypothesis, not a theorem about every Collatz orbit. -/
namespace Collatz.CoefficientSuffix
open ShadowTerminal

theorem prefix_maximum (p : Nat → Rat) (N : Nat) :
    ∃ m, m ≤ N ∧ ∀ k, k ≤ N → p k ≤ p m := by
  induction N with
  | zero =>
    refine ⟨0, Nat.le_refl 0, ?_⟩
    intro k hk
    have : k = 0 := by omega
    simp [this]
  | succ N ih =>
    obtain ⟨m, hm, hmax⟩ := ih
    by_cases h : p (N + 1) ≤ p m
    · refine ⟨m, by omega, ?_⟩
      intro k hk
      by_cases hkN : k ≤ N
      · exact hmax k hkN
      · have : k = N + 1 := by omega
        simpa [this] using h
    · refine ⟨N + 1, Nat.le_refl _, ?_⟩
      intro k hk
      by_cases hkN : k ≤ N
      · have := hmax k hkN
        grind
      · have : k = N + 1 := by omega
        simp [this]

/-- Eventual domination by the initial value suffices; convergence is not
needed as an additional premise. -/
theorem global_maximum_of_tail_bound (p : Nat → Rat) (N : Nat)
    (htail : ∀ k, N ≤ k → p k ≤ p 0) :
    ∃ m, m ≤ N ∧ ∀ k, p k ≤ p m := by
  obtain ⟨m, hm, hmax⟩ := prefix_maximum p N
  refine ⟨m, hm, ?_⟩
  intro k
  by_cases hk : k ≤ N
  · exact hmax k hk
  · exact Rat.le_trans (htail k (by omega)) (hmax 0 (Nat.zero_le N))

theorem multiplier_shift (c : Nat → Nat) (m k : Nat) :
    multiplier (m + k) c = multiplier m c * multiplier k (fun i => c (m + i)) := by
  induction m generalizing c with
  | zero => simp [multiplier]
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [multiplier, ih]
    have he : (fun i => c (m + i + 1)) = (fun i => c (m + 1 + i)) := by
      funext i
      congr 1
      omega
    rw [he]
    grind

theorem multiplier_pos (c : Nat → Nat) (hc : ∀ i, 0 < c i) (L : Nat) :
    0 < multiplier L c := by
  induction L generalizing c with
  | zero => simp only [multiplier]; grind
  | succ L ih =>
    have ht := ih (fun i => c (i + 1)) (fun i => hc (i + 1))
    have hp : (0 : Rat) < (c 0 : Rat) := Rat.natCast_lt_natCast.mpr (hc 0)
    have hdiv : (0 : Rat) < (c 0 : Rat) / 3 := by grind
    exact Rat.mul_pos hdiv ht

/-- A maximum of the inverse multiplier selects a suffix all of whose
inverse multipliers are at most one. For c_i=2^a_i this means
2^(a_m+...+a_(m+k-1)) <= 3^k for every k. -/
theorem no_crossing_suffix (c : Nat → Nat) (hc : ∀ i, 0 < c i)
    (N : Nat) (htail : ∀ k, N ≤ k → multiplier k c ≤ 1) :
    ∃ m, m ≤ N ∧ ∀ k, multiplier k (fun i => c (m + i)) ≤ 1 := by
  obtain ⟨m, hm, hmax⟩ := global_maximum_of_tail_bound (fun k => multiplier k c) N htail
  refine ⟨m, hm, ?_⟩
  intro k
  have h := hmax (m + k)
  rw [multiplier_shift] at h
  have hp := multiplier_pos c hc m
  apply Rat.le_of_mul_le_mul_left (b := 1) (c := multiplier m c) _ hp
  simpa using h

/-- If every suffix has a coefficient crossing, the original multiplier
must exceed one arbitrarily late. This contradicts a tail bounded by one,
but no such tail bound is asserted unconditionally. -/
theorem crossings_force_late_growth (c : Nat → Nat) (hc : ∀ i, 0 < c i)
    (hcross : ∀ m, ∃ k, 1 < multiplier k (fun i => c (m + i)))
    (N : Nat) : ∃ k, N ≤ k ∧ 1 < multiplier k c := by
  apply Classical.byContradiction
  intro h
  have htail : ∀ k, N ≤ k → multiplier k c ≤ 1 := by
    intro k hk
    have hnot : ¬ 1 < multiplier k c := by
      intro hp
      exact h ⟨k, hk, hp⟩
    grind
  obtain ⟨m, _, hm⟩ := no_crossing_suffix c hc N htail
  obtain ⟨k, hk⟩ := hcross m
  have := hm k
  grind

end Collatz.CoefficientSuffix
