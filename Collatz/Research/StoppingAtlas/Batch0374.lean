import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0374

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2657. -/
theorem bounds_12_2657 : exactInterval 12 2657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2657 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2657) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2657 : oddCount 2657 12 = 7 ∧ acceleratedOrbit 12 2657 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2657 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2657) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2657.1, data_12_2657.2]

/-- Complete interval computation for depth 12, residue 2658. -/
theorem bounds_12_2658 : exactInterval 12 2658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2658 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2658) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2658 : oddCount 2658 12 = 6 ∧ acceleratedOrbit 12 2658 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2658 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2658) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2658.1, data_12_2658.2]

/-- Complete interval computation for depth 12, residue 2659. -/
theorem bounds_12_2659 : exactInterval 12 2659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2659 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2659) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2659 : oddCount 2659 12 = 6 ∧ acceleratedOrbit 12 2659 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2659 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2659) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2659.1, data_12_2659.2]

/-- Complete interval computation for depth 12, residue 2660. -/
theorem bounds_12_2660 : exactInterval 12 2660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2660 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2660) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2660 : oddCount 2660 12 = 6 ∧ acceleratedOrbit 12 2660 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2660 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2660) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2660.1, data_12_2660.2]

/-- Complete interval computation for depth 12, residue 2661. -/
theorem bounds_12_2661 : exactInterval 12 2661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2661 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2661) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2661 : oddCount 2661 12 = 6 ∧ acceleratedOrbit 12 2661 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2661 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2661) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2661.1, data_12_2661.2]

/-- Complete interval computation for depth 12, residue 2662. -/
theorem bounds_12_2662 : exactInterval 12 2662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2662 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2662) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2662 : oddCount 2662 12 = 6 ∧ acceleratedOrbit 12 2662 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2662 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2662) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2662.1, data_12_2662.2]

/-- Complete interval computation for depth 12, residue 2663. -/
theorem bounds_12_2663 : exactInterval 12 2663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2663 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2663) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2663 : oddCount 2663 12 = 8 ∧ acceleratedOrbit 12 2663 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2663 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2663) = 3 ^ 8 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2663.1, data_12_2663.2]

/-- Complete interval computation for depth 12, residue 2664. -/
theorem bounds_12_2664 : exactInterval 12 2664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2664 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2664) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2664 : oddCount 2664 12 = 5 ∧ acceleratedOrbit 12 2664 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2664 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2664) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2664.1, data_12_2664.2]

/-- Complete interval computation for depth 12, residue 2665. -/
theorem bounds_12_2665 : exactInterval 12 2665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2665 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2665) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2665 : oddCount 2665 12 = 7 ∧ acceleratedOrbit 12 2665 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2665 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2665) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2665.1, data_12_2665.2]

/-- Complete interval computation for depth 12, residue 2666. -/
theorem bounds_12_2666 : exactInterval 12 2666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2666 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2666) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2666 : oddCount 2666 12 = 5 ∧ acceleratedOrbit 12 2666 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2666 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2666) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2666.1, data_12_2666.2]

/-- Complete interval computation for depth 12, residue 2667. -/
theorem bounds_12_2667 : exactInterval 12 2667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2667 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2667) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2667 : oddCount 2667 12 = 6 ∧ acceleratedOrbit 12 2667 = 475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2667 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2667) = 3 ^ 6 * m + 475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2667.1, data_12_2667.2]

/-- Complete interval computation for depth 12, residue 2668. -/
theorem bounds_12_2668 : exactInterval 12 2668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2668 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2668) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2668 : oddCount 2668 12 = 8 ∧ acceleratedOrbit 12 2668 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2668 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2668) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2668.1, data_12_2668.2]

/-- Complete interval computation for depth 12, residue 2669. -/
theorem bounds_12_2669 : exactInterval 12 2669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2669 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2669) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2669 : oddCount 2669 12 = 8 ∧ acceleratedOrbit 12 2669 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2669 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2669) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2669.1, data_12_2669.2]

/-- Complete interval computation for depth 12, residue 2670. -/
theorem bounds_12_2670 : exactInterval 12 2670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2670 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2670) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2670 : oddCount 2670 12 = 8 ∧ acceleratedOrbit 12 2670 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2670 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2670) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2670.1, data_12_2670.2]

/-- Complete interval computation for depth 12, residue 2671. -/
theorem bounds_12_2671 : exactInterval 12 2671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2671 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2671) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2671 : oddCount 2671 12 = 9 ∧ acceleratedOrbit 12 2671 = 12842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2671 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2671) = 3 ^ 9 * m + 12842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2671.1, data_12_2671.2]

end Collatz.Research.StoppingAtlas.Batch0374
