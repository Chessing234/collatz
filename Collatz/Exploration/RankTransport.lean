import Collatz.Exploration.RankReduction
import Collatz.Exploration.ResiduePotential
import Collatz.Core.Reach

/-!
# Transport of arbitrary ranks between Collatz conventions

A standard ranking function is automatically an accelerated ranking function.
The reverse implication needs a transformation: an odd state has doubled
rank, while an even state has the doubled rank of its half, plus one. The
extra one pays for the forced intermediate even state omitted by acceleration.

This construction proves an equivalence of ranking-function existence without
assuming Collatz. It also transports the finite-residue monotonicity obstruction
to the standard map. None of the results construct an unconditional rank.
-/
namespace Collatz.Exploration.RankTransport

open RankReduction ResiduePotential Reach

/-- Strict decrease above 1 for the accelerated transition. -/
def AccRanking (P : Nat → Nat) : Prop :=
  ∀ n, 1 < n → P (acceleratedStep n) < P n

/-- Removing a forced intermediate state preserves strict decrease. -/
theorem accelerated_of_standard {P : Nat → Nat} (hP : Ranking P) : AccRanking P := by
  intro n hn
  by_cases he : n%2 = 0
  · rw [accStep_eq_step_of_even he]
    exact hP n hn
  · have ho : n%2 = 1 := by omega
    have hs : 1 < step n := by rw [step_odd (by omega) ho]; omega
    rw [accStep_eq_step_step_of_odd (by omega) ho]
    exact Nat.lt_trans (hP (step n) hs) (hP n hn)

/-- Lift an accelerated potential to the standard states, paying for the
omitted expansion via the half-state rank and a one-unit phase correction. -/
def liftRank (P : Nat → Nat) (n : Nat) : Nat :=
  if n%2 = 0 then 2*P (n/2)+1 else 2*P n

/-- Odd states carry twice their original accelerated rank. -/
theorem lift_odd {P : Nat → Nat} {n : Nat} (ho : n%2 = 1) :
    liftRank P n = 2*P n := by
  rw [liftRank, if_neg (by omega : ¬ n%2 = 0)]

/-- Even states carry the doubled half-state rank and the phase unit. -/
theorem lift_even {P : Nat → Nat} {n : Nat} (he : n%2 = 0) :
    liftRank P n = 2*P (n/2)+1 := by
  rw [liftRank, if_pos he]

/-- The phase correction makes every standard step strictly decreasing. -/
theorem standard_of_accelerated {P : Nat → Nat} (hP : AccRanking P) :
    Ranking (liftRank P) := by
  intro n hn
  by_cases he : n%2 = 0
  · have hs : step n = n/2 := step_even (by omega) he
    have hp : 0 < n/2 := by omega
    rw [lift_even he, hs]
    by_cases hehalf : (n/2)%2 = 0
    · have hgt : 1 < n/2 := by omega
      have hd := hP (n/2) hgt
      rw [acceleratedStep, if_pos hehalf] at hd
      rw [lift_even hehalf]
      omega
    · have hohalf : (n/2)%2 = 1 := by omega
      rw [lift_odd hohalf]
      omega
  · have ho : n%2 = 1 := by omega
    have hs : step n = 3*n+1 := step_odd (by omega) ho
    have hse : (step n)%2 = 0 := by rw [hs]; omega
    have hhalf : (step n)/2 = acceleratedStep n := by
      rw [hs, acceleratedStep, if_neg he]
    have hd := hP n hn
    rw [lift_odd ho, lift_even hse, hhalf]
    omega

/-- The lifted rank is bounded by twice the original rank plus the phase unit
on the nontrivial positive domain. -/
theorem lift_bound {P : Nat → Nat} (hP : AccRanking P) {n : Nat} (hn : 1 < n) :
    liftRank P n ≤ 2*P n+1 := by
  by_cases he : n%2 = 0
  · have hd := hP n hn
    rw [acceleratedStep, if_pos he] at hd
    rw [lift_even he]
    omega
  · rw [lift_odd (by omega : n%2 = 1)]
    omega

/-- Arbitrary accelerated ranks are exactly as strong as arbitrary standard ranks. -/
theorem ranking_exists_iff :
    (∃ P, AccRanking P) ↔ (∃ Q, Ranking Q) := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨liftRank P, standard_of_accelerated hP⟩
  · rintro ⟨Q, hQ⟩
    exact ⟨Q, accelerated_of_standard hQ⟩

/-- Existence of an arbitrary accelerated rank is also equivalent to Collatz. -/
theorem acc_ranking_exists_iff_collatz :
    (∃ P, AccRanking P) ↔ CollatzConjecture :=
  ranking_exists_iff.trans ranking_exists_iff_collatz

/-- Residue-monotone standard candidates also fail, despite the difference in
intermediate states: a standard rank would itself be an accelerated rank. -/
theorem no_residue_monotone_standard {M : Nat} {P : Nat → Nat}
    (hM : 0 < M) (hP : ResidueMonotone M P) : ¬ Ranking P := by
  intro hR
  exact no_single_step_potential hM hP (accelerated_of_standard hR)

/-- A nonnegative piecewise affine potential cannot rank the standard map. -/
theorem no_affine_standard (M : Nat) (a b : Nat → Nat) (hM : 0 < M) :
    ¬ Ranking (fun n => a (n%M)*n+b (n%M)) :=
  no_residue_monotone_standard hM (affine_residue_monotone M a b)

/-- An accelerated rank yields a standard stopping-time bound with a phase cost. -/
theorem standard_hitting_bound {P : Nat → Nat} (hP : AccRanking P)
    {n : Nat} (hn : 1 < n) :
    ∃ k, k ≤ 2*P n+1 ∧ orbit k n = 1 := by
  obtain ⟨k, hk, he⟩ := reaches_within_rank (standard_of_accelerated hP) n (by omega)
  exact ⟨k, Nat.le_trans hk (lift_bound hP hn), he⟩

end Collatz.Exploration.RankTransport
