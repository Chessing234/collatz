import Collatz.Exploration.OrbitFloor

/-!
# Natural-valued ranking functions: exact scope and limitation

A natural-valued potential that strictly decreases at every standard step
above 1 proves Collatz by induction on the potential, even when the potential
is not monotone as a function of the input. Conversely, convergence supplies
such a potential: the least number of standard steps needed to reach 1.

Thus searching for an unrestricted ranking function is exactly as strong as
Collatz. The converse construction is noncomputable and assumes convergence;
it is not a usable independent proof or a new effective stopping-time bound.
This clarifies the distinction between the modular monotonicity obstruction
and the much wider class of possible nonmonotone potentials.
-/
namespace Collatz.Exploration.RankReduction

open OrbitFloor

/-- A natural rank strictly decreases at every nonterminal positive state. -/
def Ranking (P : Nat → Nat) : Prop :=
  ∀ n, 1 < n → P (step n) < P n

/-- Well-founded induction on an arbitrary rank proves convergence.
Input size is allowed to increase along a transition. -/
theorem collatz_of_ranking {P : Nat → Nat} (hP : Ranking P) : CollatzConjecture := by
  have h : ∀ r n, P n = r → 0 < n → Converges n := by
    intro r
    induction r using Nat.strongRecOn with
    | _ r ih =>
      intro n hr hp
      by_cases hn : n = 1
      · exact ⟨0, hn⟩
      · have hgt : 1 < n := by omega
        have hs : P (step n) < r := by rw [← hr]; exact hP n hgt
        obtain ⟨k, hk⟩ := ih (P (step n)) hs (step n) rfl (step_positive hp)
        exact ⟨k+1, by rw [orbit_succ_steps]; exact hk⟩
  intro n hp
  exact h (P n) n rfl hp

/-- Least hitting time of 1 when it exists; 0 is a default on failed inputs.
The default has no proof-theoretic power: all specifications require success. -/
noncomputable def hittingTime (n : Nat) : Nat := by
  classical
  exact if h : Converges n then Classical.choose (Minimum.exists_min_lt h) else 0

/-- The chosen time is successful and is no larger than any successful time. -/
theorem hittingTime_spec {n : Nat} (h : Converges n) :
    orbit (hittingTime n) n = 1 ∧
      ∀ k, orbit k n = 1 → hittingTime n ≤ k := by
  simp only [hittingTime, dif_pos h]
  exact Classical.choose_spec (Minimum.exists_min_lt h)

/-- The terminal value has rank zero; its later cycle is irrelevant. -/
theorem hittingTime_one : hittingTime 1 = 0 := by
  have h : Converges 1 := ⟨0, rfl⟩
  have := (hittingTime_spec h).2 0 rfl
  omega

/-- A successful nonterminal input has a strictly positive least hitting time. -/
theorem hittingTime_positive {n : Nat} (h : Converges n) (hne : n ≠ 1) :
    0 < hittingTime n := by
  have hs := (hittingTime_spec h).1
  by_cases hz : hittingTime n = 0
  · rw [hz, orbit_zero_steps] at hs
    exact False.elim (hne hs)
  · omega

/-- Convergence passes to the next state above the terminal state. -/
theorem successor_converges {n : Nat} (h : Converges n) (hne : n ≠ 1) :
    Converges (step n) := by
  have hp := hittingTime_positive h hne
  have hs := (hittingTime_spec h).1
  obtain ⟨k, hk⟩ : ∃ k, hittingTime n = k+1 := ⟨hittingTime n-1, by omega⟩
  rw [hk, orbit_succ_steps] at hs
  exact ⟨k, hs⟩

/-- The canonical successful rank decreases by exactly one per standard step. -/
theorem hittingTime_step {n : Nat} (h : Converges n) (hne : n ≠ 1) :
    hittingTime n = hittingTime (step n)+1 := by
  have hs := successor_converges h hne
  have hspec := hittingTime_spec h
  have hsspec := hittingTime_spec hs
  have hupper : hittingTime n ≤ hittingTime (step n)+1 := by
    apply hspec.2
    rw [orbit_succ_steps]
    exact hsspec.1
  have hp := hittingTime_positive h hne
  obtain ⟨k, hk⟩ : ∃ k, hittingTime n = k+1 := ⟨hittingTime n-1, by omega⟩
  have hreach : orbit k (step n) = 1 := by
    have h' := hspec.1
    rw [hk, orbit_succ_steps] at h'
    exact h'
  have hlower := hsspec.2 k hreach
  omega

/-- Under the conjecture, least hitting time is a valid global ranking. -/
theorem hittingTime_ranking (hc : CollatzConjecture) : Ranking hittingTime := by
  intro n hn
  have ht := hittingTime_step (hc n (by omega)) (by omega : n ≠ 1)
  omega

/-- Existence of an unrestricted natural ranking is equivalent to Collatz. -/
theorem ranking_exists_iff_collatz : (∃ P, Ranking P) ↔ CollatzConjecture := by
  constructor
  · rintro ⟨P, hP⟩
    exact collatz_of_ranking hP
  · intro hc
    exact ⟨hittingTime, hittingTime_ranking hc⟩

/-- Every valid rank is an upper bound for a successful hitting time.
This quantitative theorem uses only the supplied ranking hypothesis. -/
theorem reaches_within_rank {P : Nat → Nat} (hP : Ranking P) :
    ∀ n, 0 < n → ∃ k, k ≤ P n ∧ orbit k n = 1 := by
  have h : ∀ r n, P n = r → 0 < n → ∃ k, k ≤ r ∧ orbit k n = 1 := by
    intro r
    induction r using Nat.strongRecOn with
    | _ r ih =>
      intro n hr hp
      by_cases hn : n = 1
      · exact ⟨0, by omega, hn⟩
      · have hdrop : P (step n) < r := by rw [← hr]; exact hP n (by omega)
        obtain ⟨k, hk, he⟩ := ih _ hdrop (step n) rfl (step_positive hp)
        exact ⟨k+1, by omega, by rw [orbit_succ_steps]; exact he⟩
  intro n hn
  exact h (P n) n rfl hn

/-- The canonical rank is pointwise no larger than any other valid rank. -/
theorem canonical_rank_le {P : Nat → Nat} (hP : Ranking P) {n : Nat}
    (hn : 0 < n) : hittingTime n ≤ P n := by
  obtain ⟨k, hk, he⟩ := reaches_within_rank hP n hn
  exact Nat.le_trans ((hittingTime_spec ⟨k, he⟩).2 k he) hk

end Collatz.Exploration.RankReduction
