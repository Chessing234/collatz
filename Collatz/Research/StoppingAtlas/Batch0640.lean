import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0640

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2647. -/
theorem bounds_13_2647 : exactInterval 13 2647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2647 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2647) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2647 : oddCount 2647 13 = 6 ∧ acceleratedOrbit 13 2647 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2647 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2647) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2647.1, data_13_2647.2]

/-- Complete interval computation for depth 13, residue 2648. -/
theorem bounds_13_2648 : exactInterval 13 2648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2648 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2648) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2648 : oddCount 2648 13 = 5 ∧ acceleratedOrbit 13 2648 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2648 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2648) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2648.1, data_13_2648.2]

/-- Complete interval computation for depth 13, residue 2649. -/
theorem bounds_13_2649 : exactInterval 13 2649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2649 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2649) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2649 : oddCount 2649 13 = 8 ∧ acceleratedOrbit 13 2649 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2649 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2649) = 3 ^ 8 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2649.1, data_13_2649.2]

/-- Complete interval computation for depth 13, residue 2650. -/
theorem bounds_13_2650 : exactInterval 13 2650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2650 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2650) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2650 : oddCount 2650 13 = 5 ∧ acceleratedOrbit 13 2650 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2650 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2650) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2650.1, data_13_2650.2]

/-- Complete interval computation for depth 13, residue 2651. -/
theorem bounds_13_2651 : exactInterval 13 2651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2651 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2651) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2651 : oddCount 2651 13 = 9 ∧ acceleratedOrbit 13 2651 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2651 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2651) = 3 ^ 9 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2651.1, data_13_2651.2]

/-- Complete interval computation for depth 13, residue 2652. -/
theorem bounds_13_2652 : exactInterval 13 2652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2652 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2652) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2652 : oddCount 2652 13 = 5 ∧ acceleratedOrbit 13 2652 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2652 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2652) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2652.1, data_13_2652.2]

/-- Complete interval computation for depth 13, residue 2653. -/
theorem bounds_13_2653 : exactInterval 13 2653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2653 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2653) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2653 : oddCount 2653 13 = 5 ∧ acceleratedOrbit 13 2653 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2653 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2653) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2653.1, data_13_2653.2]

/-- Complete interval computation for depth 13, residue 2654. -/
theorem bounds_13_2654 : exactInterval 13 2654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2654 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2654) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2654 : oddCount 2654 13 = 8 ∧ acceleratedOrbit 13 2654 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2654 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2654) = 3 ^ 8 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2654.1, data_13_2654.2]

/-- Complete interval computation for depth 13, residue 2655. -/
theorem bounds_13_2655 : exactInterval 13 2655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2655 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2655) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2655 : oddCount 2655 13 = 8 ∧ acceleratedOrbit 13 2655 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2655 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2655) = 3 ^ 8 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2655.1, data_13_2655.2]

/-- Complete interval computation for depth 13, residue 2656. -/
theorem bounds_13_2656 : exactInterval 13 2656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2656 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2656) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2656 : oddCount 2656 13 = 6 ∧ acceleratedOrbit 13 2656 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2656 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2656) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2656.1, data_13_2656.2]

/-- Complete interval computation for depth 13, residue 2657. -/
theorem bounds_13_2657 : exactInterval 13 2657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2657 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2657) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2657 : oddCount 2657 13 = 8 ∧ acceleratedOrbit 13 2657 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2657 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2657) = 3 ^ 8 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2657.1, data_13_2657.2]

/-- Complete interval computation for depth 13, residue 2658. -/
theorem bounds_13_2658 : exactInterval 13 2658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2658 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2658) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2658 : oddCount 2658 13 = 6 ∧ acceleratedOrbit 13 2658 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2658 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2658) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2658.1, data_13_2658.2]

/-- Complete interval computation for depth 13, residue 2659. -/
theorem bounds_13_2659 : exactInterval 13 2659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2659 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2659) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2659 : oddCount 2659 13 = 6 ∧ acceleratedOrbit 13 2659 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2659 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2659) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2659.1, data_13_2659.2]

/-- Complete interval computation for depth 13, residue 2660. -/
theorem bounds_13_2660 : exactInterval 13 2660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2660 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2660) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2660 : oddCount 2660 13 = 6 ∧ acceleratedOrbit 13 2660 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2660 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2660) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2660.1, data_13_2660.2]

/-- Complete interval computation for depth 13, residue 2661. -/
theorem bounds_13_2661 : exactInterval 13 2661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2661 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2661) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2661 : oddCount 2661 13 = 6 ∧ acceleratedOrbit 13 2661 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2661 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2661) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2661.1, data_13_2661.2]

end Collatz.Research.StoppingAtlas.Batch0640
