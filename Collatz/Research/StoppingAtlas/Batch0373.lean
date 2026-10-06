import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0373

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2641. -/
theorem bounds_12_2641 : exactInterval 12 2641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2641 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2641) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2641 : oddCount 2641 12 = 8 ∧ acceleratedOrbit 12 2641 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2641 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2641) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2641.1, data_12_2641.2]

/-- Complete interval computation for depth 12, residue 2642. -/
theorem bounds_12_2642 : exactInterval 12 2642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2642 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2642) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2642 : oddCount 2642 12 = 8 ∧ acceleratedOrbit 12 2642 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2642 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2642) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2642.1, data_12_2642.2]

/-- Complete interval computation for depth 12, residue 2643. -/
theorem bounds_12_2643 : exactInterval 12 2643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2643 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2643) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2643 : oddCount 2643 12 = 8 ∧ acceleratedOrbit 12 2643 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2643 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2643) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2643.1, data_12_2643.2]

/-- Complete interval computation for depth 12, residue 2644. -/
theorem bounds_12_2644 : exactInterval 12 2644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2644 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2644) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2644 : oddCount 2644 12 = 5 ∧ acceleratedOrbit 12 2644 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2644 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2644) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2644.1, data_12_2644.2]

/-- Complete interval computation for depth 12, residue 2645. -/
theorem bounds_12_2645 : exactInterval 12 2645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2645 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2645) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2645 : oddCount 2645 12 = 5 ∧ acceleratedOrbit 12 2645 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2645 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2645) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2645.1, data_12_2645.2]

/-- Complete interval computation for depth 12, residue 2646. -/
theorem bounds_12_2646 : exactInterval 12 2646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2646 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2646) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2646 : oddCount 2646 12 = 6 ∧ acceleratedOrbit 12 2646 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2646 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2646) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2646.1, data_12_2646.2]

/-- Complete interval computation for depth 12, residue 2647. -/
theorem bounds_12_2647 : exactInterval 12 2647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2647 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2647) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2647 : oddCount 2647 12 = 6 ∧ acceleratedOrbit 12 2647 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2647 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2647) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2647.1, data_12_2647.2]

/-- Complete interval computation for depth 12, residue 2648. -/
theorem bounds_12_2648 : exactInterval 12 2648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2648 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2648) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2648 : oddCount 2648 12 = 4 ∧ acceleratedOrbit 12 2648 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2648 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2648) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2648.1, data_12_2648.2]

/-- Complete interval computation for depth 12, residue 2649. -/
theorem bounds_12_2649 : exactInterval 12 2649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2649 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2649) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2649 : oddCount 2649 12 = 7 ∧ acceleratedOrbit 12 2649 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2649 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2649) = 3 ^ 7 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2649.1, data_12_2649.2]

/-- Complete interval computation for depth 12, residue 2650. -/
theorem bounds_12_2650 : exactInterval 12 2650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2650 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2650) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2650 : oddCount 2650 12 = 4 ∧ acceleratedOrbit 12 2650 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2650 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2650) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2650.1, data_12_2650.2]

/-- Complete interval computation for depth 12, residue 2651. -/
theorem bounds_12_2651 : exactInterval 12 2651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2651 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2651) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2651 : oddCount 2651 12 = 8 ∧ acceleratedOrbit 12 2651 = 4249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2651 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2651) = 3 ^ 8 * m + 4249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2651.1, data_12_2651.2]

/-- Complete interval computation for depth 12, residue 2652. -/
theorem bounds_12_2652 : exactInterval 12 2652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2652 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2652) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2652 : oddCount 2652 12 = 4 ∧ acceleratedOrbit 12 2652 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2652 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2652) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2652.1, data_12_2652.2]

/-- Complete interval computation for depth 12, residue 2653. -/
theorem bounds_12_2653 : exactInterval 12 2653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2653 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2653) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2653 : oddCount 2653 12 = 4 ∧ acceleratedOrbit 12 2653 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2653 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2653) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2653.1, data_12_2653.2]

/-- Complete interval computation for depth 12, residue 2654. -/
theorem bounds_12_2654 : exactInterval 12 2654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2654 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2654) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2654 : oddCount 2654 12 = 8 ∧ acceleratedOrbit 12 2654 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2654 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2654) = 3 ^ 8 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2654.1, data_12_2654.2]

/-- Complete interval computation for depth 12, residue 2655. -/
theorem bounds_12_2655 : exactInterval 12 2655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2655 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2655) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2655 : oddCount 2655 12 = 8 ∧ acceleratedOrbit 12 2655 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2655 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2655) = 3 ^ 8 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2655.1, data_12_2655.2]

/-- Complete interval computation for depth 12, residue 2656. -/
theorem bounds_12_2656 : exactInterval 12 2656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2656 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2656) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2656 : oddCount 2656 12 = 5 ∧ acceleratedOrbit 12 2656 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2656 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2656) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2656.1, data_12_2656.2]

end Collatz.Research.StoppingAtlas.Batch0373
