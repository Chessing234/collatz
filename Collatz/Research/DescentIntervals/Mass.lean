import Collatz.Research.DescentIntervals.Refinement
import Collatz.Research.RefinementAtlas.Histogram

/-!
# Conservation of finite interval membership under refinement

An exact first-descent interval can be partitioned by the residue of its class
index. Refinement changes its two boundaries but preserves the number of
successful indices whenever that number is finite. This extends the earlier
one-sided exception conservation law to intervals with two finite endpoints.
-/
namespace Collatz.Research.DescentIntervals
open RefinementAtlas

/-- Moving the parent boundary right cannot move a refined cutoff left. -/
theorem cutoff_monotone {l u s q : Nat} (hs : 0 < s) (hlu : l ≤ u) :
    refinedCutoff l s q ≤ refinedCutoff u s q := by
  have hu := (cutoff_transport (t := u) (q := q) (m := refinedCutoff u s q) hs).mpr
    (Nat.le_refl _)
  exact (cutoff_transport hs).mp (Nat.le_trans hlu hu)

/-- Number of integers in a finite interval with these endpoints. -/
def finiteSize (l u : Nat) : Nat := u - l

/-- Sum of successful indices in the first d refinement digits. -/
def refinedMass (l u s : Nat) : Nat → Nat
  | 0 => 0
  | d + 1 => refinedMass l u s d +
      (refinedCutoff u s d - refinedCutoff l s d)

/-- When the parent bounds are ordered, subtracting their prefix masses is exact. -/
theorem refinedMass_balance {l u s : Nat} (hs : 0 < s) (hlu : l ≤ u) :
    ∀ d, refinedMass l u s d + exceptionMass l s d = exceptionMass u s d := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [refinedMass, exceptionMass]
    have h := cutoff_monotone (q := d) hs hlu
    omega

/-- Reversed endpoints give zero membership in every refinement digit. -/
theorem refinedMass_empty {l u s : Nat} (hs : 0 < s) (hul : u ≤ l) :
    ∀ d, refinedMass l u s d = 0 := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [refinedMass, ih, Nat.zero_add]
    exact Nat.sub_eq_zero_of_le (cutoff_monotone hs hul)

/-- All canonical digits preserve the finite parent cardinality exactly. -/
theorem refinedMass_conserved {l u s : Nat} (hs : 0 < s) :
    refinedMass l u s s = finiteSize l u := by
  by_cases hlu : l ≤ u
  · have h := refinedMass_balance hs hlu s
    rw [exceptionMass_conserved hs, exceptionMass_conserved hs] at h
    unfold finiteSize
    omega
  · rw [refinedMass_empty hs (by omega)]
    unfold finiteSize
    omega

/-- Euclidean quotient and remainder give the unique digit carrying an index. -/
theorem membership_partition (I : IndexInterval) {s i : Nat} (hs : 0 < s) :
    I.Contains i ↔ (pullback I s (i % s)).Contains (i / s) := by
  rw [pullback_spec I hs, Nat.div_add_mod]

/-- A new partition cannot manufacture exact first descent for a failing input. -/
theorem exact_membership_partition (k r : Nat) {s i : Nat} (hs : 0 < s) :
    stoppingTime (2 ^ k * i + r) k ↔
      (pullback (exactInterval k r) s (i % s)).Contains (i / s) := by
  rw [← exactInterval_spec, ← membership_partition _ hs]

/-- Finite exact-time solution counts survive every positive refinement factor. -/
theorem exact_finite_mass {k r l u s : Nat}
    (h : exactInterval k r = ⟨l, some u⟩) (hs : 0 < s) :
    (∀ m, stoppingTime (2 ^ k * m + r) k ↔ l ≤ m ∧ m < u) ∧
    refinedMass l u s s = u - l := by
  constructor
  · intro m
    exact exact_of_certificate h m
  · exact refinedMass_conserved hs

end Collatz.Research.DescentIntervals
