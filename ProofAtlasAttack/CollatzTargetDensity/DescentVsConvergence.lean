import CollatzTargetDensity.ProofChain

/-!
What least-counterexample conditioning does, and does not, give the tail
argument. All maps and sets here concern the actual ordinary Collatz map.
These theorems do not assert that a counterexample exists.
-/
namespace CollatzTargetDensity.DescentVsConvergence
open Erdos1135 ProofChain
noncomputable section

/-- A counterexample which nevertheless drops at its very first step. -/
def badFirstDrop : Set ℕ := {n | n ∈ rawBad ∧ collatzStep n < n}

theorem step_double (n : ℕ) : collatzStep (2 * n) = n := by
  rw [collatzStep_eq_div_two_of_even (by exact even_two_mul n)]
  omega

theorem double_bad {n : ℕ} (hn : n ∈ rawBad) : 2 * n ∈ rawBad := by
  refine ⟨by have := hn.1; omega, ?_⟩
  intro h
  exact hn.2 (reaches_one_forward (reaches_of_step_eq (step_double n)) h)

theorem double_bad_first_drop {n : ℕ} (hn : n ∈ rawBad) :
    2 * n ∈ badFirstDrop := by
  refine ⟨double_bad hn, ?_⟩
  rw [step_double]
  have := hn.1
  omega

/-- The distinction survives counting: doubling embeds every bad source
below X/2 into bad sources below X which immediately drop. -/
theorem count_bad_half_le_first_drop (X : ℕ) :
    Terras.natCount rawBad (X / 2) ≤ Terras.natCount badFirstDrop X := by
  classical
  let F := (Finset.range (X / 2)).filter (fun n => n ∈ rawBad)
  let D := F.image (fun n => 2 * n)
  have hcard : D.card = Terras.natCount rawBad (X / 2) := by
    dsimp [D]
    rw [Finset.card_image_of_injective _ (by intro a b h; dsimp at h; omega)]
    rw [Terras.natCount_eq_count, Nat.count_eq_card_filter_range]
  have hX : D ⊆ Finset.range X := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    apply Finset.mem_range.mpr
    omega
  have hD : (D : Set ℕ) ⊆ badFirstDrop := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    exact double_bad_first_drop (Finset.mem_filter.mp ha).2
  rw [← hcard]
  exact ND.PositiveDensity.finset_card_le_natCount_of_subset_range hX hD

/-- If any counterexample exists, a positive lower natural density of
counterexamples would have finite stopping time, indeed stopping time one.
Consequently finite stopping time almost everywhere cannot be substituted
for convergence almost everywhere in the predecessor-density argument. -/
theorem bad_first_drop_positive_density (hbad : rawBad.Nonempty) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ≤ (Terras.natCount badFirstDrop X : ℝ) := by
  obtain ⟨c, hc, X₀, hcount⟩ := counterexamples_positive_density hbad
  refine ⟨c / 4, by positivity, max (2 * X₀) 4, ?_⟩
  intro X hX
  have hhalf : X₀ ≤ X / 2 := by omega
  have hquarter : (X : ℝ) / 4 ≤ (X / 2 : ℕ) := by
    have h : X ≤ 4 * (X / 2) := by omega
    have h' : (X : ℝ) ≤ 4 * (X / 2 : ℕ) := by exact_mod_cast h
    linarith
  have hmono : (Terras.natCount rawBad (X / 2) : ℝ) ≤
      Terras.natCount badFirstDrop X := by
    exact_mod_cast count_bad_half_le_first_drop X
  calc
    c / 4 * (X : ℝ) = c * ((X : ℝ) / 4) := by ring
    _ ≤ c * (X / 2 : ℕ) := mul_le_mul_of_nonneg_left hquarter hc.le
    _ ≤ (Terras.natCount rawBad (X / 2) : ℝ) := hcount _ hhalf
    _ ≤ _ := hmono

/-- Even the pointwise claim restricted to immediate descenders is
equivalent to full convergence. It cannot serve as an easier proved link
from a stopping-time theorem to the conjecture. -/
theorem first_drop_implies_convergence_iff_collatz :
    (∀ n : ℕ, 0 < n → collatzStep n < n → Reaches n 1) ↔ collatzProp := by
  constructor
  · intro h n hn
    have hdrop : collatzStep (2 * n) < 2 * n := by rw [step_double]; omega
    exact reaches_one_forward (reaches_of_step_eq (step_double n))
      (h (2 * n) (by omega) hdrop)
  · intro h n hn _
    exact h n hn

theorem avoids_subset_bad {B : ℕ} (hB : 1 < B) : avoidsBelow B ⊆ rawBad := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  rintro ⟨k, hk⟩
  have h := hn.2 k
  rw [hk] at h
  omega

/-- At every fixed threshold between 2 and the least counterexample,
the exceptional tail is exactly the set of all counterexamples. Lowering
the threshold within this range does not shrink that set at all. -/
theorem avoids_eq_bad_of_least {m B : ℕ} (hm : LeastBad m)
    (hB : 1 < B) (hBm : B ≤ m) : avoidsBelow B = rawBad := by
  apply Set.Subset.antisymm (avoids_subset_bad hB)
  intro n hn
  have h := bad_subset_avoids_of_least hm hn
  exact ⟨h.1, fun k => hBm.trans (h.2 k)⟩

/-- Raising the threshold loses the literal predecessor-set inclusion
used in the existing proof chain. This alone makes no density claim:
failure of inclusion need not cause a positive density loss. -/
theorem successor_predecessors_not_subset_higher_tail {m B : ℕ}
    (hm : LeastBad m) (hBm : m < B) :
    ¬ rawReaches (3 * m + 1) ⊆ avoidsBelow B := by
  intro h
  have hmreach : m ∈ rawReaches (3 * m + 1) :=
    ⟨hm.1.1, reaches_of_step_eq
      (collatzStep_eq_three_mul_add_one_of_odd (least_bad_odd hm))⟩
  have hzero := (h hmreach).2 0
  simpa using (not_le_of_gt hBm hzero)

end
end CollatzTargetDensity.DescentVsConvergence
