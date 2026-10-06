import Collatz.Research.CoefficientDescent.Basic

/-!
# Effective Terras transfer on every dyadic cylinder

At fixed depth the actual and coefficient stopping events agree for all
sufficiently large class indices. A finite, nonempty exact-time interval is
therefore evidence of a disagreement of the two stopping events, never a new
kind of asymptotic density contribution. This is a formalization of the
classical finite-exception mechanism, not a priority claim.
-/
namespace Collatz.Research.CoefficientDescent

open FirstLightDescent FirstDescentClass DescentIntervals

/-- Every prefix odd count is constant on its containing depth-k dyadic class. -/
theorem oddCount_class_prefix {j k : Nat} (hj : j ≤ k) (r m : Nat) :
    oddCount (2 ^ k * m + r) j = oddCount r j := by
  rw [Density.oddCount_mod (2 ^ k * m + r) j, Density.oddCount_mod r j]
  congr 1
  rw [split_modulus hj, Nat.mul_assoc, Nat.mul_add_mod]

/-- Unlike actual descent at small starts, the coefficient event is exactly periodic. -/
theorem firstLight_class (k r m : Nat) :
    FirstLight (2 ^ k * m + r) k ↔ FirstLight r k := by
  unfold FirstLight
  rw [oddCount_class_prefix (Nat.le_refl k)]
  constructor
  · rintro ⟨hl, hp⟩
    refine ⟨hl, fun j hj => ?_⟩
    have h := hp j hj
    rwa [oddCount_class_prefix (Nat.le_of_lt hj)] at h
  · rintro ⟨hl, hp⟩
    refine ⟨hl, fun j hj => ?_⟩
    rw [oddCount_class_prefix (Nat.le_of_lt hj)]
    exact hp j hj

/-- A conservative explicit threshold, valid simultaneously for every prefix. -/
def transferCutoff (k r : Nat) : Nat :=
  Sum.sumRange (k + 1) (fun j => acceleratedOrbit j r) + 1

/-- Every prefix constant is strictly below the transfer cutoff. -/
theorem prefix_below_cutoff {j k : Nat} (hj : j ≤ k) (r : Nat) :
    acceleratedOrbit j r < transferCutoff k r := by
  have := Sum.le_sumRange (fun i => acceleratedOrbit i r) (show j < k + 1 by omega)
  unfold transferCutoff
  omega

/-- At a light prefix the dyadic slope gap is at least one. -/
theorem prefix_slope_lt {j k r : Nat} (hj : j ≤ k)
    (hl : 3 ^ oddCount r j < 2 ^ j) :
    3 ^ oddCount r j * 2 ^ (k - j) < 2 ^ k := by
  rw [split_modulus hj]
  exact Nat.mul_lt_mul_of_lt_of_le hl (Nat.le_refl _) (Arith.two_pow_pos _)

/-- An explicit class-index threshold suffices for descent at any light prefix. -/
theorem prefix_drop_after_constant {j k r m : Nat} (hj : j ≤ k)
    (hl : 3 ^ oddCount r j < 2 ^ j) (hm : acceleratedOrbit j r < m) :
    acceleratedOrbit j (2 ^ k * m + r) < 2 ^ k * m + r := by
  rw [prefix_orbit hj]
  have hs := prefix_slope_lt hj hl
  have hmul := Nat.mul_le_mul_right m (show 3 ^ oddCount r j * 2 ^ (k-j) + 1 ≤ 2 ^ k by omega)
  rw [Nat.add_mul, Nat.one_mul] at hmul
  omega

/-- First coefficient crossing is equivalent to actual first descent after the explicit cutoff. -/
theorem eventual_exact_iff {k r m : Nat} (hm : transferCutoff k r ≤ m) :
    stoppingTime (2 ^ k * m + r) k ↔ FirstLight r k := by
  constructor
  · intro hs
    have hl := AffineObstruction.light_of_drop hs.2.1
    rw [oddCount_class_prefix (Nat.le_refl k)] at hl
    refine ⟨hl, fun j hj => ?_⟩
    apply Classical.byContradiction
    intro hheavy
    have hb := prefix_below_cutoff (Nat.le_of_lt hj) r
    have hd := prefix_drop_after_constant (Nat.le_of_lt hj) (by omega : 3 ^ oddCount r j < 2 ^ j)
      (show acceleratedOrbit j r < m by omega)
    have hn := FirstDescentResidue.before_first_descent hs j hj
    omega
  · intro hf
    have hb := prefix_below_cutoff (Nat.le_refl k) r
    exact stopping_of_firstLight_drop ((firstLight_class k r m).mpr hf)
      (prefix_drop_after_constant (Nat.le_refl k) hf.1 (by omega))

/-- Effective finite-exception statement for the existing interval classifier. -/
theorem interval_eventual_iff {k r m : Nat} (hm : transferCutoff k r ≤ m) :
    (exactInterval k r).Contains m ↔ FirstLight r k := by
  rw [exactInterval_spec]
  exact eventual_exact_iff hm

/-- The exact-time index set is unbounded precisely for admissible coefficient words. -/
theorem unbounded_iff_firstLight (k r : Nat) :
    (∀ M, ∃ m, M ≤ m ∧ (exactInterval k r).Contains m) ↔ FirstLight r k := by
  constructor
  · intro h
    obtain ⟨m, hm, hs⟩ := h (transferCutoff k r)
    exact (interval_eventual_iff hm).mp hs
  · intro hf M
    let m := max M (transferCutoff k r)
    exact ⟨m, Nat.le_max_left _ _, (interval_eventual_iff (Nat.le_max_right _ _)).mpr hf⟩

/-- A nonadmissible coefficient word confines any actual first descents below a finite cutoff. -/
theorem bounded_of_not_firstLight {k r : Nat} (hf : ¬ FirstLight r k) :
    ∀ m, (exactInterval k r).Contains m → m < transferCutoff k r := by
  intro m hm
  apply Classical.byContradiction
  intro h
  exact hf ((interval_eventual_iff (by omega)).mp hm)

/-- A finite nonempty interval witnesses a discrepancy at one of its represented inputs. -/
theorem finite_interval_witness {k r : Nat}
    (hb : ∃ B, ∀ m, (exactInterval k r).Contains m → m < B)
    (hne : ∃ m, (exactInterval k r).Contains m) :
    ∃ n, 1 < n ∧ stoppingTime n k ∧ ¬ FirstLight n k := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨m, hm⟩ := hne
  have hs := (exactInterval_spec k r m).mp hm
  refine ⟨2 ^ k * m + r, start_gt_one hs, hs, ?_⟩
  intro hf
  have hu := (unbounded_iff_firstLight k r).mpr ((firstLight_class k r m).mp hf)
  obtain ⟨u, huB, hus⟩ := hu B
  have := hB u hus
  omega

/-- Conversely, a delayed actual first descent creates a finite nonempty interval. -/
theorem finite_interval_of_discrepancy {k r m : Nat}
    (hs : stoppingTime (2 ^ k * m + r) k)
    (hf : ¬ FirstLight (2 ^ k * m + r) k) :
    (∃ B, ∀ u, (exactInterval k r).Contains u → u < B) ∧
      ∃ u, (exactInterval k r).Contains u := by
  have hr : ¬ FirstLight r k := fun h => hf ((firstLight_class k r m).mpr h)
  exact ⟨⟨transferCutoff k r, bounded_of_not_firstLight hr⟩,
    ⟨m, (exactInterval_spec k r m).mpr hs⟩⟩

end Collatz.Research.CoefficientDescent
