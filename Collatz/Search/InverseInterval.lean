import Collatz.Structure.InverseSpreadBoundary

/-!
# Executable inverse search inside a proposed cycle interval

Both accelerated inverse branches are explored. Every visited value must lie
inside the interval and avoid multiples of three. A positive cycle within
that interval survives every depth; a failed finite search excludes it.
Finite survival alone asserts a path, not a cycle.
-/
namespace Collatz.InverseInterval
open AccCycle CycleInverseSpread

/-- Complete classification of the two possible accelerated predecessors. -/
theorem step_predecessors (p v : Nat) : acceleratedStep p=v ↔
    p=2*v ∨ (v%3=2 ∧ p=(2*v-1)/3) := by
  constructor
  · intro h
    by_cases he : p%2=0
    · left
      rw [acceleratedStep, if_pos he] at h
      omega
    · right
      rw [acceleratedStep, if_neg he] at h
      constructor <;> omega
  · intro h
    rcases h with h | ⟨hr, h⟩
    · subst p
      simp [acceleratedStep]
    · subst p
      have ho : ((2*v-1)/3)%2=1 := by omega
      rw [acceleratedStep, if_neg (by omega)]
      omega

/-- Values allowed by an interval and the cycle's exclusion of multiples of 3. -/
def Allowed (lo hi v : Nat) : Prop := lo≤v ∧ v≤hi ∧ v%3≠0
instance (lo hi v : Nat) : Decidable (Allowed lo hi v) := inferInstanceAs
  (Decidable (lo≤v ∧ v≤hi ∧ v%3≠0))

/-- A reverse path of exactly k transitions, with every state allowed. -/
def BackPath (lo hi : Nat) : Nat → Nat → Prop
  | 0, v => Allowed lo hi v
  | k+1, v => Allowed lo hi v ∧ ∃ p, acceleratedStep p=v ∧ BackPath lo hi k p

/-- Finite branching search, retaining only allowed inverse paths. -/
def survives (lo hi : Nat) : Nat → Nat → Bool
  | 0, v => decide (Allowed lo hi v)
  | k+1, v => decide (Allowed lo hi v) &&
      (survives lo hi k (2*v) ||
        (decide (v%3=2) && survives lo hi k ((2*v-1)/3)))

/-- Exact semantics: success is existence of a finite reverse path. -/
theorem survives_iff (lo hi k v : Nat) : survives lo hi k v=true ↔ BackPath lo hi k v := by
  induction k generalizing v with
  | zero => simp only [survives, BackPath, decide_eq_true_eq]
  | succ k ih =>
    simp only [survives, BackPath, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨hv, hp | ⟨hr, hp⟩⟩
      · exact ⟨hv, 2*v, (step_predecessors _ _).mpr (Or.inl rfl), hp⟩
      · exact ⟨hv, (2*v-1)/3, (step_predecessors _ _).mpr (Or.inr ⟨hr, rfl⟩), hp⟩
    · rintro ⟨hv, p, ht, hp⟩
      rcases (step_predecessors p v).mp ht with he | ⟨hr, he⟩
      · subst p; exact ⟨hv, Or.inl hp⟩
      · subst p; exact ⟨hv, Or.inr ⟨hr, hp⟩⟩

/-- Every path includes its starting value in the allowed set. -/
theorem path_allowed {lo hi k v : Nat} (h : BackPath lo hi k v) : Allowed lo hi v := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

/-- Truncating a reverse path preserves admissibility. -/
theorem path_truncate {lo hi a b v : Nat} (hab : a≤b) (h : BackPath lo hi b v) :
    BackPath lo hi a v := by
  induction a generalizing b v with
  | zero => exact path_allowed h
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      obtain ⟨hv, p, ht, hp⟩ := h
      exact ⟨hv, p, ht, ih (by omega) hp⟩

/-- Survival sets decrease with depth. A rejected input never reappears at a
larger search depth. -/
theorem survives_truncate {lo hi a b v : Nat} (hab : a≤b)
    (h : survives lo hi b v=true) : survives lo hi a v=true :=
  (survives_iff _ _ _ _).mpr (path_truncate hab ((survives_iff _ _ _ _).mp h))

/-- Every point of a positive cycle confined to the interval survives any
finite search depth, because its actual predecessor is always among the branches. -/
theorem cycle_survives {lo hi m L : Nat} (hm : 0<m) (h : AccIsCycleOf m L)
    (hband : ∀ i, lo≤acceleratedOrbit i m ∧ acceleratedOrbit i m≤hi)
    (k : Nat) {v : Nat} (hv : ∃ i, acceleratedOrbit i m=v) :
    survives lo hi k v=true := by
  apply (survives_iff _ _ _ _).mpr
  induction k generalizing v with
  | zero =>
    obtain ⟨i, rfl⟩ := hv
    exact ⟨(hband i).1, (hband i).2, by
      have := CycleModThree.not_three_dvd_orbit hm h i
      omega⟩
  | succ k ih =>
    obtain ⟨p, hp, ht, _⟩ := cycle_predecessor hm h hv
    refine ⟨?_, p, ht, ih hp⟩
    obtain ⟨i, rfl⟩ := hv
    exact ⟨(hband i).1, (hband i).2, by
      have := CycleModThree.not_three_dvd_orbit hm h i
      omega⟩

/-- A false result is a sound finite certificate excluding a positive cycle
through the input whose values all fit in the proposed interval. -/
theorem rejection_excludes_cycle {lo hi k m : Nat} (hm : 0<m)
    (hc : survives lo hi k m=false) :
    ¬∃ L, AccIsCycleOf m L ∧
      (∀ i, lo≤acceleratedOrbit i m ∧ acceleratedOrbit i m≤hi) := by
  rintro ⟨L, hL, hb⟩
  have hs := cycle_survives hm hL hb k (v := m) ⟨0, rfl⟩
  rw [hc] at hs
  contradiction

/-- The trivial cycle survives every depth within [1,2]. -/
theorem trivial_cycle_survives (k : Nat) : survives 1 2 k 1=true := by
  apply cycle_survives (by decide : 0<1) AccCycle.accIsCycleOf_one
  intro i
  rw [CycleExtremes.accOrbit_mod_period AccCycle.accIsCycleOf_one.2]
  have hi : i%2=0 ∨ i%2=1 := by omega
  rcases hi with hi | hi <;> rw [hi] <;> decide
  exact ⟨0, rfl⟩

/-- Finite survival need not continue one more level. -/
theorem finite_survival_can_end : survives 7 56 4 7=true ∧
    survives 7 56 5 7=false := by decide

end Collatz.InverseInterval
