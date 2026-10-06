import Collatz.Search.InverseInterval
import Collatz.Strategy.FiniteOrbitCertificates

/-!
# A complete finite decision depth for inverse-interval search

Once a reverse path has as many transitions as the interval has integer
values, it repeats. Determinism puts its endpoint on the repeated cycle.
Thus survival at this explicit depth is equivalent to a positive cycle
through the tested value confined to the interval. Shorter survival remains
only a finite-path statement.
-/
namespace Collatz.InverseInterval
open AccCycle

/-- Read a reverse path as a forward orbit from its oldest predecessor. -/
theorem path_as_forward {lo hi k v : Nat} (h : BackPath lo hi k v) :
    ∃ p, acceleratedOrbit k p=v ∧
      ∀ i, i≤k → Allowed lo hi (acceleratedOrbit i p) := by
  induction k generalizing v with
  | zero =>
    refine ⟨v, rfl, ?_⟩
    intro i hi
    have he : i=0 := by omega
    subst i
    exact h
  | succ k ih =>
    obtain ⟨hv, p, ht, hp⟩ := h
    obtain ⟨q, hq, hb⟩ := ih hp
    have hend : acceleratedOrbit (k+1) q=v := by
      rw [acceleratedOrbit_succ_step, hq, ht]
    refine ⟨q, hend, ?_⟩
    intro i hi
    by_cases hik : i≤k
    · exact hb i hik
    · have he : i=k+1 := by omega
      rw [he, hend]
      exact hv

/-- The integer interval contains at most hi-lo+1 states. Survival for that
many transitions forces the endpoint itself onto a cycle in the interval. -/
theorem cycle_of_long_path {lo hi v : Nat}
    (h : BackPath lo hi (hi-lo+1) v) :
    ∃ L, AccIsCycleOf v L ∧ ∀ t, Allowed lo hi (acceleratedOrbit t v) := by
  let K := hi-lo+1
  obtain ⟨p, hend, hb⟩ := path_as_forward h
  have hval : ∀ i, i≤K → acceleratedOrbit i p-lo<K := by
    intro i hiK
    have ha := hb i hiK
    dsimp [Allowed] at ha
    dsimp [K]
    omega
  obtain ⟨i, j, hij, hj, he⟩ := Pigeonhole.exists_repeat hval (Nat.le_refl _)
  have hiK : i≤K := by omega
  have hai := hb i hiK
  have haj := hb j hj
  have heq : acceleratedOrbit i p=acceleratedOrbit j p := by
    dsimp [Allowed] at hai haj
    omega
  have hcyc : AccIsCycleOf (acceleratedOrbit i p) (j-i) := by
    refine ⟨by omega, ?_⟩
    rw [acceleratedOrbit_add, Nat.sub_add_cancel (by omega)]
    exact heq.symm
  have hv : acceleratedOrbit (K-i) (acceleratedOrbit i p)=v := by
    rw [acceleratedOrbit_add, Nat.sub_add_cancel hiK]
    exact hend
  refine ⟨j-i, ?_, ?_⟩
  · rw [← hv]
    exact accIsCycleOf_orbit hcyc (K-i)
  · intro t
    obtain ⟨s, hs, hred⟩ := FiniteOrbitCertificates.repeat_reduces hij heq (t+K)
    have hsK : s≤K := by omega
    have had := hb s hsK
    have horb : acceleratedOrbit t v=acceleratedOrbit s p := by
      rw [← hend, acceleratedOrbit_add]
      exact hred
    rw [horb]
    exact had

/-- At the explicit decision depth, survival is equivalent to an actual
cycle through the input with every orbit value allowed. -/
theorem survives_decision_iff (lo hi v : Nat) :
    survives lo hi (hi-lo+1) v=true ↔
      ∃ L, AccIsCycleOf v L ∧ ∀ t, Allowed lo hi (acceleratedOrbit t v) := by
  constructor
  · intro h
    exact cycle_of_long_path ((survives_iff _ _ _ _).mp h)
  · rintro ⟨L, hL, hb⟩
    have hv := hb 0
    have hpos : 0<v := by
      change lo≤v ∧ v≤hi ∧ v%3≠0 at hv
      omega
    exact cycle_survives hpos hL (fun t => ⟨(hb t).1, (hb t).2.1⟩) _ ⟨0, rfl⟩

/-- A cycle which stays in a natural-number interval is positive exactly when
it also obeys the modulo-three filter. This version exposes positivity. -/
theorem survives_decision_positive_iff (lo hi v : Nat) :
    survives lo hi (hi-lo+1) v=true ↔
      0<v ∧ ∃ L, AccIsCycleOf v L ∧
        (∀ t, lo≤acceleratedOrbit t v ∧ acceleratedOrbit t v≤hi) := by
  constructor
  · intro h
    obtain ⟨L, hL, hb⟩ := (survives_decision_iff lo hi v).mp h
    have ha := hb 0
    have hp : 0<v := by
      change lo≤v ∧ v≤hi ∧ v%3≠0 at ha
      omega
    exact ⟨hp, L, hL, fun t => ⟨(hb t).1, (hb t).2.1⟩⟩
  · rintro ⟨hv, L, hL, hb⟩
    exact cycle_survives hv hL hb _ ⟨0, rfl⟩

/-- After the decision depth, increasing the depth cannot change the answer. -/
theorem survives_stable {lo hi v k : Nat} (hk : hi-lo+1≤k) :
    survives lo hi k v=survives lo hi (hi-lo+1) v := by
  cases hshort : survives lo hi (hi-lo+1) v with
  | false =>
    cases hlong : survives lo hi k v with
    | false => rfl
    | true =>
      have := survives_truncate hk hlong
      rw [hshort] at this
      contradiction
  | true =>
    obtain ⟨hv, L, hL, hb⟩ := (survives_decision_positive_iff lo hi v).mp hshort
    exact cycle_survives hv hL hb k ⟨0, rfl⟩

/-- Every finite depth survives exactly when the explicit decision depth does. -/
theorem all_depths_iff_decision (lo hi v : Nat) :
    (∀ k, survives lo hi k v=true) ↔ survives lo hi (hi-lo+1) v=true := by
  constructor
  · intro h; exact h _
  · intro h k
    obtain ⟨hv, L, hL, hb⟩ := (survives_decision_positive_iff lo hi v).mp h
    exact cycle_survives hv hL hb k ⟨0, rfl⟩

/-- The decision excludes zero despite its fixed point, as specified by the
positive-cycle interface. -/
theorem zero_decision_rejected : survives 0 0 1 0=false := by decide

/-- A concrete short survivor from the previous module fails at decision depth. -/
theorem seven_decision_rejected : survives 7 56 50 7=false := by decide

end Collatz.InverseInterval
