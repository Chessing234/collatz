import Collatz.Search.InverseIntervalLayers

/-!
# Safe early stopping for inverse interval layers

Compare membership sets, rather than list equality: cycles can rotate list
order and duplicate multiplicities are irrelevant. Once one round preserves
membership, every later round does too. A fuel-bounded runner returns the
same periodic set as the complete computation and records rounds performed.
-/
namespace Collatz.InverseInterval

/-- Equality of represented sets, allowing order and multiplicity differences. -/
def SameMembers (xs ys : List Nat) : Prop := ∀ v, v∈xs ↔ v∈ys

/-- Finite executable comparison of membership in both directions. -/
def sameMembersCheck (xs ys : List Nat) : Bool :=
  xs.all (fun v => ys.contains v) && ys.all (fun v => xs.contains v)

theorem sameMembersCheck_iff (xs ys : List Nat) :
    sameMembersCheck xs ys=true ↔ SameMembers xs ys := by
  simp only [sameMembersCheck, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨hxy, hyx⟩ v
    exact ⟨hxy v, hyx v⟩
  · intro h
    exact ⟨fun v hv => (h v).mp hv, fun v hv => (h v).mpr hv⟩

/-- Advancing and filtering depends only on membership, not multiplicity. -/
theorem advance_sameMembers {lo hi : Nat} {xs ys : List Nat} (h : SameMembers xs ys) :
    SameMembers (advanceLayer lo hi xs) (advanceLayer lo hi ys) := by
  intro v
  simp only [mem_advanceLayer]
  constructor
  · rintro ⟨hv, p, hp, ht⟩
    exact ⟨hv, p, (h p).mp hp, ht⟩
  · rintro ⟨hv, p, hp, ht⟩
    exact ⟨hv, p, (h p).mpr hp, ht⟩

/-- Unshortened iteration from an arbitrary initial list. -/
def evolve (lo hi : Nat) : Nat → List Nat → List Nat
  | 0, xs => xs
  | k+1, xs => evolve lo hi k (advanceLayer lo hi xs)

theorem evolve_succ_last (lo hi k : Nat) (xs : List Nat) :
    evolve lo hi (k+1) xs=advanceLayer lo hi (evolve lo hi k xs) := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => exact ih (advanceLayer lo hi xs)

/-- This iteration agrees with the existing complete layer computation. -/
theorem evolve_intervalStates (lo hi k : Nat) :
    evolve lo hi k (intervalStates lo hi)=layers lo hi k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [evolve_succ_last, ih]; rfl

/-- One equality of membership is enough for all subsequent rounds. -/
theorem evolve_fixed_members {lo hi : Nat} {xs : List Nat}
    (h : SameMembers (advanceLayer lo hi xs) xs) (k : Nat) :
    SameMembers (evolve lo hi k xs) xs := by
  induction k with
  | zero => intro v; exact Iff.rfl
  | succ k ih =>
    rw [evolve_succ_last]
    intro v
    exact (advance_sameMembers ih v).trans (h v)

/-- The result includes actual rounds evaluated, bounded by the supplied fuel. -/
structure PruneResult where
  states : List Nat
  rounds : Nat
  deriving Repr, DecidableEq

/-- Return after a membership fixed point, or when fuel is exhausted. -/
def pruneStable (lo hi : Nat) : Nat → List Nat → PruneResult
  | 0, xs => ⟨xs, 0⟩
  | k+1, xs =>
      let next := advanceLayer lo hi xs
      if sameMembersCheck next xs then ⟨next, 1⟩
      else
        let result := pruneStable lo hi k next
        ⟨result.states, result.rounds+1⟩

/-- Early termination preserves the membership result of the full fuel budget. -/
theorem pruneStable_correct (lo hi fuel : Nat) (xs : List Nat) :
    SameMembers (pruneStable lo hi fuel xs).states (evolve lo hi fuel xs) := by
  induction fuel generalizing xs with
  | zero => intro v; exact Iff.rfl
  | succ fuel ih =>
    simp only [pruneStable]
    split
    · rename_i hcheck
      have hf := (sameMembersCheck_iff _ _).mp hcheck
      intro v
      exact (hf v).trans ((evolve_fixed_members hf (fuel+1) v).symm)
    · exact ih (advanceLayer lo hi xs)

/-- The reported number of evaluated rounds never exceeds the fuel. -/
theorem pruneStable_rounds_le (lo hi fuel : Nat) (xs : List Nat) :
    (pruneStable lo hi fuel xs).rounds≤fuel := by
  induction fuel generalizing xs with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    simp only [pruneStable]
    split
    · change 1≤fuel+1
      omega
    · exact Nat.succ_le_succ (ih (advanceLayer lo hi xs))

/-- Early stopping cannot increase the list length. -/
theorem pruneStable_length_le (lo hi fuel : Nat) (xs : List Nat) :
    (pruneStable lo hi fuel xs).states.length≤xs.length := by
  induction fuel generalizing xs with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    simp only [pruneStable]
    split
    · exact advance_length_le lo hi xs
    · exact Nat.le_trans (ih _) (advance_length_le lo hi xs)

/-- A complete bounded-interval cycle computation, with early stopping enabled. -/
def earlyDecision (lo hi : Nat) : PruneResult :=
  pruneStable lo hi (hi-lo+1) (intervalStates lo hi)

/-- The shortened result has exactly the complete positive-cycle semantics. -/
theorem earlyDecision_iff (lo hi v : Nat) :
    v∈(earlyDecision lo hi).states ↔
      0<v ∧ ∃ L, AccCycle.AccIsCycleOf v L ∧
        (∀ t, lo≤acceleratedOrbit t v ∧ acceleratedOrbit t v≤hi) := by
  have h := pruneStable_correct lo hi (hi-lo+1) (intervalStates lo hi) v
  rw [evolve_intervalStates] at h
  exact h.trans (decision_layer_iff lo hi v)

/-- The completed early-stop computation obeys the explicit interval-width
bounds on both rounds and retained entries. -/
theorem earlyDecision_resources (lo hi : Nat) :
    (earlyDecision lo hi).rounds≤hi-lo+1 ∧
    (earlyDecision lo hi).states.length≤hi-lo+1 := by
  refine ⟨pruneStable_rounds_le lo hi _ _, ?_⟩
  apply Nat.le_trans (pruneStable_length_le lo hi _ _)
  exact layer_length_le lo hi 0

/-- The rotating two-cycle is detected as stable after one round, despite
its reversed list order. -/
theorem trivial_early_stop : earlyDecision 1 2=⟨[2,1], 1⟩ := by decide

/-- Duplicate multiplicities do not prevent a valid membership comparison. -/
theorem duplicate_membership_check : sameMembersCheck [1,2,1] [2,1]=true := by decide

end Collatz.InverseInterval
