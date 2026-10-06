import Collatz.Research.DescentIntervals.Classifier

/-!
# Cycle candidates from the same affine solver

A positive-depth fixed endpoint lies in the intersection of two affine
half-spaces. Unequal powers of two and three imply at most one candidate per
class. Candidate membership is a genuine periodicity statement, but does not
specify the least period and does not exclude every nontrivial cycle.
-/
namespace Collatz.Research.DescentIntervals

/-- All class indices returning to their initial value after k steps. -/
def periodicInterval (k r : Nat) : IndexInterval :=
  intersect
    (solveLE (3 ^ oddCount r k) (acceleratedOrbit k r) (2 ^ k) r)
    (solveLE (2 ^ k) r (3 ^ oddCount r k) (acceleratedOrbit k r))

/-- A second complete use of the solver: exact periodicity rather than descent. -/
theorem periodicInterval_spec (k r m : Nat) :
    (periodicInterval k r).Contains m ↔
      acceleratedOrbit k (2 ^ k * m + r) = 2 ^ k * m + r := by
  rw [Congruence.accOrbit_pow_two_mul_add]
  unfold periodicInterval
  rw [contains_intersect, solveLE_spec, solveLE_spec]
  omega

/-- Two unequal affine slopes can cross at most once over natural indices. -/
theorem affine_fixed_unique {A P b r m t : Nat} (hne : A ≠ P)
    (hm : A * m + b = P * m + r) (ht : A * t + b = P * t + r) : m = t := by
  by_cases hs : A < P
  · have hp : P = A + (P - A) := by omega
    have hem : P * m = A * m + (P - A) * m := by rw [hp, Nat.add_mul]; simp
    have het : P * t = A * t + (P - A) * t := by rw [hp, Nat.add_mul]; simp
    exact Nat.mul_left_cancel (show 0 < P - A by omega) (by omega)
  · have ha : A = P + (A - P) := by omega
    have hem : A * m = P * m + (A - P) * m := by rw [ha, Nat.add_mul]; simp
    have het : A * t = P * t + (A - P) * t := by rw [ha, Nat.add_mul]; simp
    exact Nat.mul_left_cancel (show 0 < A - P by omega) (by omega)

/-- At positive depth there is at most one periodic index per dyadic class. -/
theorem periodic_index_unique {k r m t : Nat} (hk : 0 < k)
    (hm : (periodicInterval k r).Contains m)
    (ht : (periodicInterval k r).Contains t) : m = t := by
  have hem := (periodicInterval_spec k r m).mp hm
  have het := (periodicInterval_spec k r t).mp ht
  rw [Congruence.accOrbit_pow_two_mul_add] at hem het
  exact affine_fixed_unique (FirstDescentClass.endpoint_slope_ne hk) hem het

/-- For contracting slopes the exact cycle equation includes its offset and divisibility. -/
theorem contracting_periodic_iff {k r m : Nat}
    (hc : 3 ^ oddCount r k < 2 ^ k) :
    (periodicInterval k r).Contains m ↔
      r ≤ acceleratedOrbit k r ∧
      (2 ^ k - 3 ^ oddCount r k) * m = acceleratedOrbit k r - r := by
  rw [periodicInterval_spec, Congruence.accOrbit_pow_two_mul_add]
  have hp : 2 ^ k = 3 ^ oddCount r k + (2 ^ k - 3 ^ oddCount r k) := by omega
  have he : 2 ^ k * m = 3 ^ oddCount r k * m + (2 ^ k - 3 ^ oddCount r k) * m := by
    rw [hp, Nat.add_mul]; simp
  omega

/-- Any periodic candidate on a contracting cylinder needs exact gap divisibility. -/
theorem periodic_gap_divides {k r m : Nat} (hc : 3 ^ oddCount r k < 2 ^ k)
    (hm : (periodicInterval k r).Contains m) :
    (2 ^ k - 3 ^ oddCount r k) ∣ (acceleratedOrbit k r - r) := by
  have h := (contracting_periodic_iff hc).mp hm
  exact ⟨m, h.2.symm⟩

/-- Periodicity at k and first descent at k are mutually exclusive. -/
theorem periodic_excludes_exact {k r m : Nat}
    (hp : (periodicInterval k r).Contains m) :
    ¬ (exactInterval k r).Contains m := by
  intro hd
  have he := (periodicInterval_spec k r m).mp hp
  have hl := ((exactInterval_spec k r m).mp hd).2.1
  omega

end Collatz.Research.DescentIntervals
