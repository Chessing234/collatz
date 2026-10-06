import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0835

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5642. -/
theorem bounds_13_5642 : exactInterval 13 5642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5642 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5642) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5642 : oddCount 5642 13 = 4 ∧ acceleratedOrbit 13 5642 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5642 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5642) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5642.1, data_13_5642.2]

/-- Complete interval computation for depth 13, residue 5643. -/
theorem bounds_13_5643 : exactInterval 13 5643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5643 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5643) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5643 : oddCount 5643 13 = 6 ∧ acceleratedOrbit 13 5643 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5643 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5643) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5643.1, data_13_5643.2]

/-- Complete interval computation for depth 13, residue 5644. -/
theorem bounds_13_5644 : exactInterval 13 5644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5644 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5644) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5644 : oddCount 5644 13 = 4 ∧ acceleratedOrbit 13 5644 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5644 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5644) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5644.1, data_13_5644.2]

/-- Complete interval computation for depth 13, residue 5645. -/
theorem bounds_13_5645 : exactInterval 13 5645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5645 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5645) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5645 : oddCount 5645 13 = 4 ∧ acceleratedOrbit 13 5645 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5645 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5645) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5645.1, data_13_5645.2]

/-- Complete interval computation for depth 13, residue 5646. -/
theorem bounds_13_5646 : exactInterval 13 5646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5646 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5646) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5646 : oddCount 5646 13 = 8 ∧ acceleratedOrbit 13 5646 = 4526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5646 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5646) = 3 ^ 8 * m + 4526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5646.1, data_13_5646.2]

/-- Complete interval computation for depth 13, residue 5647. -/
theorem bounds_13_5647 : exactInterval 13 5647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5647 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5647) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5647 : oddCount 5647 13 = 8 ∧ acceleratedOrbit 13 5647 = 4526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5647 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5647) = 3 ^ 8 * m + 4526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5647.1, data_13_5647.2]

/-- Complete interval computation for depth 13, residue 5648. -/
theorem bounds_13_5648 : exactInterval 13 5648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5648 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5648) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5648 : oddCount 5648 13 = 6 ∧ acceleratedOrbit 13 5648 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5648 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5648) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5648.1, data_13_5648.2]

/-- Complete interval computation for depth 13, residue 5649. -/
theorem bounds_13_5649 : exactInterval 13 5649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5649 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5649) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5649 : oddCount 5649 13 = 4 ∧ acceleratedOrbit 13 5649 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5649 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5649) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5649.1, data_13_5649.2]

/-- Complete interval computation for depth 13, residue 5650. -/
theorem bounds_13_5650 : exactInterval 13 5650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5650 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5650) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5650 : oddCount 5650 13 = 8 ∧ acceleratedOrbit 13 5650 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5650 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5650) = 3 ^ 8 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5650.1, data_13_5650.2]

/-- Complete interval computation for depth 13, residue 5651. -/
theorem bounds_13_5651 : exactInterval 13 5651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5651 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5651) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5651 : oddCount 5651 13 = 8 ∧ acceleratedOrbit 13 5651 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5651 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5651) = 3 ^ 8 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5651.1, data_13_5651.2]

/-- Complete interval computation for depth 13, residue 5652. -/
theorem bounds_13_5652 : exactInterval 13 5652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5652 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5652) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5652 : oddCount 5652 13 = 6 ∧ acceleratedOrbit 13 5652 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5652 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5652) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5652.1, data_13_5652.2]

/-- Complete interval computation for depth 13, residue 5653. -/
theorem bounds_13_5653 : exactInterval 13 5653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5653 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5653) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5653 : oddCount 5653 13 = 6 ∧ acceleratedOrbit 13 5653 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5653 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5653) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5653.1, data_13_5653.2]

/-- Complete interval computation for depth 13, residue 5654. -/
theorem bounds_13_5654 : exactInterval 13 5654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5654 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5654) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5654 : oddCount 5654 13 = 8 ∧ acceleratedOrbit 13 5654 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5654 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5654) = 3 ^ 8 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5654.1, data_13_5654.2]

/-- Complete interval computation for depth 13, residue 5655. -/
theorem bounds_13_5655 : exactInterval 13 5655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5655 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5655) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5655 : oddCount 5655 13 = 8 ∧ acceleratedOrbit 13 5655 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5655 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5655) = 3 ^ 8 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5655.1, data_13_5655.2]

/-- Complete interval computation for depth 13, residue 5656. -/
theorem bounds_13_5656 : exactInterval 13 5656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5656 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5656) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5656 : oddCount 5656 13 = 6 ∧ acceleratedOrbit 13 5656 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5656 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5656) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5656.1, data_13_5656.2]

end Collatz.Research.StoppingAtlas.Batch0835
