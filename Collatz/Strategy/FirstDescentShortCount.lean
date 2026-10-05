import Collatz.Strategy.FirstDescentShort
import Collatz.Search.FirstDescentCertificate
import Collatz.Core.Sum

/-!
# Exact finite counts for the short first-descent classes

Counts use positive inputs `[1,N]`, with the input one correctly excluded
from both descent classes. The first two classes are disjoint and contain
exactly three quarters of `[2,4*q+1]`. No later stopping time is assumed.
-/

namespace Collatz.FirstDescentResidue
open Collatz.Sum

/-- Count inputs whose exact stopping time is the specified index. -/
def exactTimeCount (k N : Nat) : Nat :=
  sumRange N (fun i => if Search.firstDescentB (i + 1) k then 1 else 0)

/-- The exact-time-one checker is a parity test on all positive inputs. -/
theorem firstDescentB_one_iff (i : Nat) :
    Search.firstDescentB (i + 1) 1 = true ↔ (i + 1) % 2 = 0 := by
  rw [Search.firstDescentB_spec, stoppingTime_one_iff_even (by omega)]

/-- The exact-time-two checker excludes one and selects one modulo four. -/
theorem firstDescentB_two_iff (i : Nat) :
    Search.firstDescentB (i + 1) 2 = true ↔ 0 < i ∧ i % 4 = 0 := by
  rw [Search.firstDescentB_spec, stoppingTime_two_iff]
  omega

/-- Every inclusive cutoff contains exactly floor(N/2) time-one inputs. -/
theorem exactTimeCount_one (N : Nat) : exactTimeCount 1 N = N / 2 := by
  have he : exactTimeCount 1 N =
      sumRange N (fun i => if (i + 1) % 2 = 0 then 1 else 0) := by
    unfold exactTimeCount
    apply sumRange_congr
    intro i _
    simp only [firstDescentB_one_iff]
  rw [he]
  clear he
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [sumRange_succ, ih]
    split <;> omega

/-- Every inclusive cutoff contains exactly floor((N-1)/4) time-two inputs. -/
theorem exactTimeCount_two (N : Nat) : exactTimeCount 2 N = (N - 1) / 4 := by
  have he : exactTimeCount 2 N =
      sumRange N (fun i => if 0 < i ∧ i % 4 = 0 then 1 else 0) := by
    unfold exactTimeCount
    apply sumRange_congr
    intro i _
    simp only [firstDescentB_two_iff]
  rw [he]
  clear he
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [sumRange_succ, ih]
    by_cases hN : N = 0
    · subst N
      decide
    · split <;> omega

/-- No cutoff contains a time-three input. -/
theorem exactTimeCount_three (N : Nat) : exactTimeCount 3 N = 0 := by
  unfold exactTimeCount
  have he : sumRange N (fun i => if Search.firstDescentB (i + 1) 3 then 1 else 0) =
      sumRange N (fun _ => 0) := by
    apply sumRange_congr
    intro i _
    have hf : Search.firstDescentB (i + 1) 3 ≠ true := by
      intro h
      exact no_stoppingTime_three _ ((Search.firstDescentB_spec _ _).mp h)
    simp [hf]
  rw [he, sumRange_const]
  omega

/-- Exact first-descent checkers at distinct indices cannot both succeed. -/
theorem firstDescentB_disjoint {n j k : Nat} (hj : Search.firstDescentB n j = true)
    (hk : Search.firstDescentB n k = true) : j = k :=
  stoppingTime_unique ((Search.firstDescentB_spec _ _).mp hj)
    ((Search.firstDescentB_spec _ _).mp hk)

/-- Count all inputs that first descend within two steps. -/
def withinTwoCount (N : Nat) : Nat :=
  sumRange N (fun i => if Search.firstDescentB (i + 1) 1 ||
    Search.firstDescentB (i + 1) 2 then 1 else 0)

/-- The union count equals the sum because the two exact-time classes are disjoint. -/
theorem withinTwoCount_eq (N : Nat) :
    withinTwoCount N = exactTimeCount 1 N + exactTimeCount 2 N := by
  unfold withinTwoCount exactTimeCount
  rw [← sumRange_add]
  apply sumRange_congr
  intro i _
  by_cases h1 : Search.firstDescentB (i + 1) 1 = true
  · have h2 : Search.firstDescentB (i + 1) 2 ≠ true := by
      intro h2
      have hj := firstDescentB_disjoint h1 h2
      omega
    simp [h1, h2]
  · by_cases h2 : Search.firstDescentB (i + 1) 2 = true
    · simp [h1, h2]
    · simp [h1, h2]

/-- Exact early-descent count for every inclusive positive cutoff. -/
theorem withinTwoCount_exact (N : Nat) :
    withinTwoCount N = N / 2 + (N - 1) / 4 := by
  rw [withinTwoCount_eq, exactTimeCount_one, exactTimeCount_two]

/-- Exactly three quarters of `[2,4*q+1]` first descend by time two. -/
theorem withinTwoCount_aligned (q : Nat) : withinTwoCount (4 * q + 1) = 3 * q := by
  rw [withinTwoCount_exact]
  omega

/-- A kernel-evaluated finite regression of the orbit-based union checker. -/
theorem withinTwoCount_forty_one : withinTwoCount 41 = 30 := by decide

end Collatz.FirstDescentResidue
