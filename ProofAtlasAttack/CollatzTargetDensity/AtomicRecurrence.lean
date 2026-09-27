import CollatzTargetDensity.ProofChain
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
A valid atomic-weight route from uniform preimage bounds to recurrence.
Existence of suitable positive summable weights and exclusion of nontrivial
cycles are explicit hypotheses; neither is established here. This argument
does not use a counting-measure mean-bound theorem.
-/
namespace CollatzTargetDensity.AtomicRecurrence
open Erdos1135 Filter ProofChain
open scoped BigOperators Topology
noncomputable section

/-- A single constant controls every iterate and every finite part of each
preimage. This is stronger than a bound for only one step. -/
def AtomicPowerBound (f : ℕ → ℕ) (w : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ k y (s : Finset ℕ), (∀ x ∈ s, 0 < x ∧ (f^[k]) x = y) →
    (∑ x ∈ s, w x) ≤ C * w y

theorem orbit_atom_le {f : ℕ → ℕ} {w : ℕ → ℝ} {C : ℝ}
    (hbound : AtomicPowerBound f w C) {x : ℕ} (hx : 0 < x) (k : ℕ) :
    w x ≤ C * w ((f^[k]) x) := by
  simpa using hbound k ((f^[k]) x) {x} (by simpa using hx)

/-- A positive initial atom cannot visit arbitrarily large integers: a
summable weight tends to zero there, while the uniform bound keeps every
visited atom above the fixed positive threshold w(x)/C. -/
theorem bounded_orbit_of_atomic_power_bound {f : ℕ → ℕ} {w : ℕ → ℝ} {C : ℝ}
    (hw : Summable w) (hC : 0 < C) (hbound : AtomicPowerBound f w C)
    {x : ℕ} (hx : 0 < x) (hwx : 0 < w x) :
    ∃ B : ℕ, ∀ k : ℕ, (f^[k]) x < B := by
  have heps : 0 < w x / C := div_pos hwx hC
  have hsmall : ∀ᶠ y : ℕ in atTop, w y < w x / C :=
    (tendsto_order.mp hw.tendsto_atTop_zero).2 _ heps
  obtain ⟨B, hB⟩ := eventually_atTop.mp hsmall
  refine ⟨B, ?_⟩
  intro k
  by_contra hnot
  have hh := (lt_div_iff₀ hC).mp (hB ((f^[k]) x) (by omega))
  have ha := orbit_atom_le hbound hx k
  nlinarith

theorem periodic_hit_of_bounded_orbit {f : ℕ → ℕ} {x B : ℕ}
    (hB : ∀ k : ℕ, (f^[k]) x < B) :
    ∃ i p : ℕ, 0 < p ∧ (f^[p]) ((f^[i]) x) = (f^[i]) x := by
  let code : ℕ → Fin B := fun k => ⟨(f^[k]) x, hB k⟩
  obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite code
  have hh : (f^[i]) x = (f^[j]) x := congrArg Fin.val heq
  have hpair : ∃ i j : ℕ, i < j ∧ (f^[i]) x = (f^[j]) x := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact ⟨i, j, hij, hh⟩
    · exact ⟨j, i, hji, hh.symm⟩
  obtain ⟨a, b, hab, hh⟩ := hpair
  refine ⟨a, b - a, by omega, ?_⟩
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le]
  exact hh.symm

/-- Conditional closing chain for the canonical ordinary Collatz map.
The two substantive inputs remain assumptions, not proved constructions. -/
theorem collatz_of_atomic_power_bound_and_cycles {w : ℕ → ℝ} {C : ℝ}
    (hw : Summable w) (hwpos : ∀ n : ℕ, 0 < n → 0 < w n)
    (hC : 0 < C) (hbound : AtomicPowerBound collatzStep w C)
    (hcycles : ∀ n : ℕ, 0 < n → ∀ p : ℕ, 0 < p →
      (collatzStep^[p]) n = n → Reaches n 1) : collatzProp := by
  intro n hn
  obtain ⟨B, hB⟩ := bounded_orbit_of_atomic_power_bound hw hC hbound hn (hwpos n hn)
  obtain ⟨i, p, hp, hper⟩ := periodic_hit_of_bounded_orbit hB
  have hr := hcycles ((collatzStep^[i]) n) (iterate_pos hn i) p hp hper
  exact (show Reaches n ((collatzStep^[i]) n) from ⟨i, rfl⟩).trans hr

/-- Strict positivity on the known cycle and its entering branch already
forces the uniform power-bound constant to exceed one. No summability or
information about unknown orbits is needed for this restriction. -/
theorem atomic_power_constant_gt_one {w : ℕ → ℝ} {C : ℝ}
    (hwpos : ∀ n : ℕ, 0 < n → 0 < w n)
    (hbound : AtomicPowerBound collatzStep w C) : 1 < C := by
  have h2 : w 2 ≤ C * w 1 := by
    simpa [collatzStep, CollatzConjecture.collatzStep] using
      orbit_atom_le hbound (by norm_num : 0 < 2) 1
  have h4 : w 4 ≤ C * w 2 := by
    simpa [collatzStep, CollatzConjecture.collatzStep] using
      orbit_atom_le hbound (by norm_num : 0 < 4) 1
  have h18 := hbound 1 4 {1, 8} (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> norm_num [collatzStep, CollatzConjecture.collatzStep])
  have h18' : w 1 + w 8 ≤ C * w 4 := by simpa using h18
  have hw1 := hwpos 1 (by norm_num)
  have hw2 := hwpos 2 (by norm_num)
  have hw4 := hwpos 4 (by norm_num)
  have hw8 := hwpos 8 (by norm_num)
  by_contra hnot
  have hle : C ≤ 1 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hle hw1.le,
    mul_le_mul_of_nonneg_right hle hw2.le, mul_le_mul_of_nonneg_right hle hw4.le]

end
end CollatzTargetDensity.AtomicRecurrence
