import Collatz.Basic
import Collatz.Core.Minimum

/-!
# Orbit floors and forward invariant obstructions

These are exact reductions, not a proof of convergence. A failed orbit has a
least reachable value. Starting at that value produces a trajectory that never
descends and avoids 1. This packages the obstruction for several techniques:
well-founded descent, trapping sets, and record-minimum arguments.
No finiteness, periodicity, probability, or boundedness assumption is used.
-/
namespace Collatz.Exploration.OrbitFloor

/-- The standard orbit eventually attains 1. -/
def Converges (n : Nat) : Prop := ∃ k, orbit k n = 1

/-- A positive orbit floor above the trivial cycle. -/
def Floor (m : Nat) : Prop := 1 < m ∧ ∀ k, m ≤ orbit k m

/-- Reaching a convergent state certifies convergence of the initial state. -/
theorem converges_of_reachable {n j : Nat}
    (h : Converges (orbit j n)) : Converges n := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k+j, by rw [orbit_add, hk]⟩

/-- Failure to reach 1 is preserved at every future state. -/
theorem failure_forward {n : Nat} (hn : ¬ Converges n) (j : Nat) :
    ¬ Converges (orbit j n) := by
  intro h
  exact hn (converges_of_reachable h)

/-- Every orbit has an attained least value, even when it is unbounded. -/
theorem attained_minimum (n : Nat) :
    ∃ j, ∀ k, orbit j n ≤ orbit k n := by
  obtain ⟨m, ⟨j, hj⟩, hmin⟩ := Minimum.exists_min_lt
    (P := fun m => ∃ j, orbit j n = m) ⟨n, 0, rfl⟩
  refine ⟨j, fun k => ?_⟩
  rw [hj]
  exact hmin (orbit k n) ⟨k, rfl⟩

/-- A least attained state is a floor for its entire future trajectory. -/
theorem minimum_future {n j : Nat}
    (hmin : ∀ k, orbit j n ≤ orbit k n) :
    ∀ k, orbit j n ≤ orbit k (orbit j n) := by
  intro k
  rw [← orbit_add]
  exact hmin (k+j)

/-- Every positive counterexample supplies a reachable floor above 1. -/
theorem floor_of_failure {n : Nat} (hpos : 0 < n)
    (hn : ¬ Converges n) : ∃ j, Floor (orbit j n) := by
  obtain ⟨j, hmin⟩ := attained_minimum n
  have hp := orbit_positive hpos j
  have hne : orbit j n ≠ 1 := by
    intro he
    exact hn ⟨j, he⟩
  exact ⟨j, by constructor; omega; exact minimum_future hmin⟩

/-- A floor above 1 cannot converge. -/
theorem failure_of_floor {m : Nat} (hm : Floor m) : ¬ Converges m := by
  rintro ⟨k, hk⟩
  have h := hm.2 k
  rw [hk] at h
  have := hm.1
  omega

/-- Eliminating all positive orbit floors is exactly the conjecture. -/
theorem no_floor_iff_collatz : (∀ m, ¬ Floor m) ↔ CollatzConjecture := by
  constructor
  · intro hf n hp
    by_cases hc : Converges n
    · exact hc
    · obtain ⟨j, hj⟩ := floor_of_failure hp hc
      exact False.elim (hf (orbit j n) hj)
  · intro hc m hm
    exact failure_of_floor hm (hc m (by have := hm.1; omega))

/-- A trapping set is closed under the standard step and excludes 1. -/
def Trap (S : Nat → Prop) : Prop :=
  (∀ n, S n → 0 < n) ∧ (¬ S 1) ∧ (∀ n, S n → S (step n))

/-- Membership persists through arbitrarily many steps. -/
theorem trap_orbit {S : Nat → Prop} (hS : Trap S) {n : Nat}
    (hn : S n) (k : Nat) : S (orbit k n) := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih => exact ih (hS.2.2 n hn)

/-- Any inhabitant of a trapping set is a positive counterexample. -/
theorem trap_failure {S : Nat → Prop} (hS : Trap S) {n : Nat}
    (hn : S n) : 0 < n ∧ ¬ Converges n := by
  refine ⟨hS.1 n hn, ?_⟩
  rintro ⟨k, hk⟩
  have hs := trap_orbit hS hn k
  rw [hk] at hs
  exact hS.2.1 hs

/-- The reachable states of any failed positive trajectory form a trap. -/
theorem reachable_trap {n : Nat} (hp : 0 < n) (hf : ¬ Converges n) :
    Trap (fun m => ∃ k, orbit k n = m) := by
  refine ⟨?_, hf, ?_⟩
  · rintro m ⟨k, rfl⟩
    exact orbit_positive hp k
  · rintro m ⟨k, rfl⟩
    exact ⟨k+1, by rw [orbit_succ_steps, orbit_step_commute]⟩

/-- No nonempty positive trapping set exists precisely when Collatz holds. -/
theorem traps_empty_iff_collatz :
    (∀ S, Trap S → ∀ n, ¬ S n) ↔ CollatzConjecture := by
  constructor
  · intro ht n hp
    by_cases hc : Converges n
    · exact hc
    · exact False.elim (ht _ (reachable_trap hp hc) n ⟨0, rfl⟩)
  · intro hc S hS n hn
    obtain ⟨hp, hf⟩ := trap_failure hS hn
    exact hf (hc n hp)

/-- A nontrivial floor cannot be even: one ordinary step would descend. -/
theorem floor_odd {m : Nat} (hm : Floor m) : m % 2 = 1 := by
  have hp : m ≠ 0 := by have := hm.1; omega
  have hmin := hm.2 1
  by_cases he : m % 2 = 0
  · simp [orbit, step, hp, he] at hmin
    have := hm.1
    omega
  · omega

/-- The residue 1 modulo 4 descends in three ordinary steps above 1. -/
theorem residue_one_descent (q : Nat) (hq : 0 < q) :
    orbit 3 (4*q+1) = 3*q+1 := by
  have h1 : step (4*q+1) = 12*q+4 := by
    rw [step, if_neg (by omega : 4*q+1 ≠ 0),
      if_neg (by omega : ¬ (4*q+1) % 2 = 0)]
    omega
  have h2 : step (12*q+4) = 6*q+2 := by
    rw [step, if_neg (by omega : 12*q+4 ≠ 0),
      if_pos (by omega : (12*q+4) % 2 = 0)]
    omega
  have h3 : step (6*q+2) = 3*q+1 := by
    rw [step, if_neg (by omega : 6*q+2 ≠ 0),
      if_pos (by omega : (6*q+2) % 2 = 0)]
    omega
  simp [orbit, h1, h2, h3]

/-- Every nontrivial orbit floor lies in the residue 3 modulo 4. -/
theorem floor_mod_four {m : Nat} (hm : Floor m) : m % 4 = 3 := by
  have ho := floor_odd hm
  have hp := hm.1
  by_cases he : m % 4 = 1
  · have hrepr : m = 4*(m/4)+1 := by omega
    have hq : 0 < m/4 := by omega
    have hd := residue_one_descent (m/4) hq
    have hmin := hm.2 3
    rw [hrepr, hd] at hmin
    omega
  · omega

end Collatz.Exploration.OrbitFloor
