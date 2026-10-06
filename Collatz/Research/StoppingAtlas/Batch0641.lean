import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0641

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2662. -/
theorem bounds_13_2662 : exactInterval 13 2662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2662 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2662) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2662 : oddCount 2662 13 = 6 ∧ acceleratedOrbit 13 2662 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2662 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2662) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2662.1, data_13_2662.2]

/-- Complete interval computation for depth 13, residue 2663. -/
theorem bounds_13_2663 : exactInterval 13 2663 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2663 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2663) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2663 : oddCount 2663 13 = 8 ∧ acceleratedOrbit 13 2663 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2663 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2663) = 3 ^ 8 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2663.1, data_13_2663.2]

/-- Complete interval computation for depth 13, residue 2664. -/
theorem bounds_13_2664 : exactInterval 13 2664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2664 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2664) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2664 : oddCount 2664 13 = 6 ∧ acceleratedOrbit 13 2664 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2664 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2664) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2664.1, data_13_2664.2]

/-- Complete interval computation for depth 13, residue 2665. -/
theorem bounds_13_2665 : exactInterval 13 2665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2665 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2665) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2665 : oddCount 2665 13 = 7 ∧ acceleratedOrbit 13 2665 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2665 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2665) = 3 ^ 7 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2665.1, data_13_2665.2]

/-- Complete interval computation for depth 13, residue 2666. -/
theorem bounds_13_2666 : exactInterval 13 2666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2666 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2666) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2666 : oddCount 2666 13 = 6 ∧ acceleratedOrbit 13 2666 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2666 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2666) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2666.1, data_13_2666.2]

/-- Complete interval computation for depth 13, residue 2667. -/
theorem bounds_13_2667 : exactInterval 13 2667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2667 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2667) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2667 : oddCount 2667 13 = 7 ∧ acceleratedOrbit 13 2667 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2667 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2667) = 3 ^ 7 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2667.1, data_13_2667.2]

/-- Complete interval computation for depth 13, residue 2668. -/
theorem bounds_13_2668 : exactInterval 13 2668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2668 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2668) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2668 : oddCount 2668 13 = 9 ∧ acceleratedOrbit 13 2668 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2668 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2668) = 3 ^ 9 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2668.1, data_13_2668.2]

/-- Complete interval computation for depth 13, residue 2669. -/
theorem bounds_13_2669 : exactInterval 13 2669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2669 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2669) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2669 : oddCount 2669 13 = 9 ∧ acceleratedOrbit 13 2669 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2669 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2669) = 3 ^ 9 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2669.1, data_13_2669.2]

/-- Complete interval computation for depth 13, residue 2670. -/
theorem bounds_13_2670 : exactInterval 13 2670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2670 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2670) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2670 : oddCount 2670 13 = 9 ∧ acceleratedOrbit 13 2670 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2670 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2670) = 3 ^ 9 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2670.1, data_13_2670.2]

/-- Complete interval computation for depth 13, residue 2671. -/
theorem bounds_13_2671 : exactInterval 13 2671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2671 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2671) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2671 : oddCount 2671 13 = 9 ∧ acceleratedOrbit 13 2671 = 6421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2671 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2671) = 3 ^ 9 * m + 6421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2671.1, data_13_2671.2]

/-- Complete interval computation for depth 13, residue 2672. -/
theorem bounds_13_2672 : exactInterval 13 2672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2672 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2672) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2672 : oddCount 2672 13 = 7 ∧ acceleratedOrbit 13 2672 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2672 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2672) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2672.1, data_13_2672.2]

/-- Complete interval computation for depth 13, residue 2673. -/
theorem bounds_13_2673 : exactInterval 13 2673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2673 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2673) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2673 : oddCount 2673 13 = 6 ∧ acceleratedOrbit 13 2673 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2673 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2673) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2673.1, data_13_2673.2]

/-- Complete interval computation for depth 13, residue 2674. -/
theorem bounds_13_2674 : exactInterval 13 2674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2674 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2674) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2674 : oddCount 2674 13 = 8 ∧ acceleratedOrbit 13 2674 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2674 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2674) = 3 ^ 8 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2674.1, data_13_2674.2]

/-- Complete interval computation for depth 13, residue 2675. -/
theorem bounds_13_2675 : exactInterval 13 2675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2675 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2675) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2675 : oddCount 2675 13 = 8 ∧ acceleratedOrbit 13 2675 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2675 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2675) = 3 ^ 8 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2675.1, data_13_2675.2]

/-- Complete interval computation for depth 13, residue 2676. -/
theorem bounds_13_2676 : exactInterval 13 2676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2676 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2676) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2676 : oddCount 2676 13 = 7 ∧ acceleratedOrbit 13 2676 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2676 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2676) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2676.1, data_13_2676.2]

end Collatz.Research.StoppingAtlas.Batch0641
