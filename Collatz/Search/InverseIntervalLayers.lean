import Collatz.Search.InverseIntervalComplete

/-!
# Finite-list implementation of inverse-interval decisions

Start with the allowed interval values. At each round, map the surviving list
forward once and discard disallowed images. Membership after k rounds is
exactly survival of a k-step inverse path. Duplicates are harmless: the list
never grows, and membership, not multiplicity, is the decision interface.
-/
namespace Collatz.InverseInterval

/-- Enumerate the interval using its width rather than its absolute endpoint.
The final filter also handles hi<lo and removes multiples of three. -/
def intervalStates (lo hi : Nat) : List Nat :=
  ((List.range (hi-lo+1)).map (fun i => lo+i)).filter (fun v => decide (Allowed lo hi v))

theorem mem_intervalStates (lo hi v : Nat) :
    v∈intervalStates lo hi ↔ Allowed lo hi v := by
  simp only [intervalStates, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    apply List.mem_map.mpr
    refine ⟨v-lo, List.mem_range.mpr ?_, ?_⟩ <;> dsimp [Allowed] at h <;> omega

/-- One pruning round advances every surviving source and keeps allowed images. -/
def advanceLayer (lo hi : Nat) (xs : List Nat) : List Nat :=
  (xs.map acceleratedStep).filter (fun v => decide (Allowed lo hi v))

theorem mem_advanceLayer (lo hi v : Nat) (xs : List Nat) :
    v∈advanceLayer lo hi xs ↔
      Allowed lo hi v ∧ ∃ p, p∈xs ∧ acceleratedStep p=v := by
  simp only [advanceLayer, List.mem_filter, List.mem_map, decide_eq_true_eq]
  exact and_comm

/-- All inverse-path endpoints are computed together, one layer at a time. -/
def layers (lo hi : Nat) : Nat → List Nat
  | 0 => intervalStates lo hi
  | k+1 => advanceLayer lo hi (layers lo hi k)

/-- Membership in a layer has the original inverse-path semantics. -/
theorem mem_layers_iff (lo hi k v : Nat) :
    v∈layers lo hi k ↔ BackPath lo hi k v := by
  induction k generalizing v with
  | zero => exact mem_intervalStates lo hi v
  | succ k ih =>
    simp only [layers, mem_advanceLayer, ih, BackPath]
    constructor
    · rintro ⟨hv, p, hp, ht⟩
      exact ⟨hv, p, ht, hp⟩
    · rintro ⟨hv, p, ht, hp⟩
      exact ⟨hv, p, hp, ht⟩

/-- The new implementation agrees with the recursive Boolean checker. -/
theorem layer_membership_iff_survives (lo hi k v : Nat) :
    v∈layers lo hi k ↔ survives lo hi k v=true :=
  (mem_layers_iff lo hi k v).trans (survives_iff lo hi k v).symm

/-- At the complete decision depth, the list contains exactly the positive
periodic points whose entire cycles fit inside the interval. -/
theorem decision_layer_iff (lo hi v : Nat) :
    v∈layers lo hi (hi-lo+1) ↔
      0<v ∧ ∃ L, AccCycle.AccIsCycleOf v L ∧
        (∀ t, lo≤acceleratedOrbit t v ∧ acceleratedOrbit t v≤hi) :=
  (layer_membership_iff_survives lo hi _ v).trans (survives_decision_positive_iff lo hi v)

/-- A round cannot increase list length, even though distinct sources can
produce duplicate images. -/
theorem advance_length_le (lo hi : Nat) (xs : List Nat) :
    (advanceLayer lo hi xs).length≤xs.length := by
  have h := List.length_filter_le (fun v => decide (Allowed lo hi v)) (xs.map acceleratedStep)
  simpa only [advanceLayer, List.length_map] using h

/-- Every layer uses at most the interval width in list entries. -/
theorem layer_length_le (lo hi k : Nat) : (layers lo hi k).length≤hi-lo+1 := by
  induction k with
  | zero =>
    have h := List.length_filter_le (fun v => decide (Allowed lo hi v))
      ((List.range (hi-lo+1)).map (fun i => lo+i))
    simpa only [layers, intervalStates, List.length_map, List.length_range] using h
  | succ k ih => exact Nat.le_trans (advance_length_le lo hi _) ih

/-- Endpoint sets decrease, even when the list order or multiplicity changes. -/
theorem layer_subset_previous (lo hi k v : Nat) (h : v∈layers lo hi (k+1)) :
    v∈layers lo hi k := by
  apply (layer_membership_iff_survives lo hi k v).mpr
  exact survives_truncate (by omega) ((layer_membership_iff_survives lo hi (k+1) v).mp h)

/-- Endpoint sets are stable past the complete depth. Equality of lists is
not claimed, because a cycle can permute the entries from round to round. -/
theorem layer_membership_stable {lo hi k v : Nat} (hk : hi-lo+1≤k) :
    v∈layers lo hi k ↔ v∈layers lo hi (hi-lo+1) := by
  rw [layer_membership_iff_survives, layer_membership_iff_survives, survives_stable hk]

/-- A Boolean membership interface for a single completed layer. -/
def layerCheck (lo hi v : Nat) : Bool := (layers lo hi (hi-lo+1)).contains v

theorem layerCheck_iff (lo hi v : Nat) : layerCheck lo hi v=true ↔
    0<v ∧ ∃ L, AccCycle.AccIsCycleOf v L ∧
      (∀ t, lo≤acceleratedOrbit t v ∧ acceleratedOrbit t v≤hi) := by
  simpa only [layerCheck, List.contains_iff_mem] using decision_layer_iff lo hi v

/-- An empty completed list is equivalent to absence of every positive cycle
confined to the interval, not just a cycle through one selected input. -/
theorem decision_layer_empty_iff (lo hi : Nat) :
    layers lo hi (hi-lo+1)=[] ↔
      ¬∃ v L, 0<v ∧ AccCycle.AccIsCycleOf v L ∧
        (∀ t, lo≤acceleratedOrbit t v ∧ acceleratedOrbit t v≤hi) := by
  constructor
  · rintro he ⟨v, L, hv, hc, hb⟩
    have hm := (decision_layer_iff lo hi v).mpr ⟨hv, L, hc, hb⟩
    rw [he] at hm
    exact List.not_mem_nil hm
  · intro hno
    cases he : layers lo hi (hi-lo+1) with
    | nil => rfl
    | cons v xs =>
      have hm : v∈layers lo hi (hi-lo+1) := by rw [he]; simp
      obtain ⟨hv, L, hc, hb⟩ := (decision_layer_iff lo hi v).mp hm
      exact False.elim (hno ⟨v, L, hv, hc, hb⟩)

/-- Multiplicity is deliberately retained: list length is not a count of
periodic points. Membership still gives the exact periodic set. -/
theorem duplicate_entries_example : layers 1 4 4=[1, 2, 1] := by decide

/-- The finite list can be empty even if shallow inverse paths exist. -/
theorem seven_layer_empty : layers 7 56 50=[] := by decide

set_option maxRecDepth 10000 in
/-- A transient point feeding the trivial cycle is not accepted as periodic. -/
theorem transient_four_rejected : layerCheck 1 100 4=false := by decide

set_option maxRecDepth 10000 in
/-- Both points of the trivial cycle are retained. -/
theorem trivial_points_retained : layerCheck 1 100 1=true ∧ layerCheck 1 100 2=true := by decide

end Collatz.InverseInterval
