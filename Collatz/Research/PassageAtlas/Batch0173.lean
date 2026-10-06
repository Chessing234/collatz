import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0173

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5636. -/
theorem bounds_15_5636 : exactInterval 15 5636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5636 : oddCount 5636 15 = 8 ∧ acceleratedOrbit 15 5636 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5636) = 3 ^ 8 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5636.1, data_15_5636.2]

/-- Complete interval computation for depth 15, residue 5637. -/
theorem bounds_15_5637 : exactInterval 15 5637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5637 : oddCount 5637 15 = 8 ∧ acceleratedOrbit 15 5637 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5637) = 3 ^ 8 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5637.1, data_15_5637.2]

/-- Complete interval computation for depth 15, residue 5638. -/
theorem bounds_15_5638 : exactInterval 15 5638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5638 : oddCount 5638 15 = 8 ∧ acceleratedOrbit 15 5638 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5638) = 3 ^ 8 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5638.1, data_15_5638.2]

/-- Complete interval computation for depth 15, residue 5639. -/
theorem bounds_15_5639 : exactInterval 15 5639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5639 : oddCount 5639 15 = 7 ∧ acceleratedOrbit 15 5639 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5639) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5639.1, data_15_5639.2]

/-- Complete interval computation for depth 15, residue 5640. -/
theorem bounds_15_5640 : exactInterval 15 5640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5640 : oddCount 5640 15 = 4 ∧ acceleratedOrbit 15 5640 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5640) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5640.1, data_15_5640.2]

/-- Complete interval computation for depth 15, residue 5641. -/
theorem bounds_15_5641 : exactInterval 15 5641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5641 : oddCount 5641 15 = 9 ∧ acceleratedOrbit 15 5641 = 3392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5641) = 3 ^ 9 * m + 3392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5641.1, data_15_5641.2]

/-- Complete interval computation for depth 15, residue 5642. -/
theorem bounds_15_5642 : exactInterval 15 5642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5642 : oddCount 5642 15 = 4 ∧ acceleratedOrbit 15 5642 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5642) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5642.1, data_15_5642.2]

/-- Complete interval computation for depth 15, residue 5643. -/
theorem bounds_15_5643 : exactInterval 15 5643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5643 : oddCount 5643 15 = 8 ∧ acceleratedOrbit 15 5643 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5643) = 3 ^ 8 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5643.1, data_15_5643.2]

/-- Complete interval computation for depth 15, residue 5644. -/
theorem bounds_15_5644 : exactInterval 15 5644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5644 : oddCount 5644 15 = 4 ∧ acceleratedOrbit 15 5644 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5644) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5644.1, data_15_5644.2]

/-- Complete interval computation for depth 15, residue 5645. -/
theorem bounds_15_5645 : exactInterval 15 5645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5645 : oddCount 5645 15 = 4 ∧ acceleratedOrbit 15 5645 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5645) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5645.1, data_15_5645.2]

/-- Complete interval computation for depth 15, residue 5646. -/
theorem bounds_15_5646 : exactInterval 15 5646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5646 : oddCount 5646 15 = 9 ∧ acceleratedOrbit 15 5646 = 3395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5646) = 3 ^ 9 * m + 3395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5646.1, data_15_5646.2]

/-- Complete interval computation for depth 15, residue 5647. -/
theorem bounds_15_5647 : exactInterval 15 5647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5647 : oddCount 5647 15 = 9 ∧ acceleratedOrbit 15 5647 = 3395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5647) = 3 ^ 9 * m + 3395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5647.1, data_15_5647.2]

/-- Complete interval computation for depth 15, residue 5648. -/
theorem bounds_15_5648 : exactInterval 15 5648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5648 : oddCount 5648 15 = 7 ∧ acceleratedOrbit 15 5648 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5648) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5648.1, data_15_5648.2]

/-- Complete interval computation for depth 15, residue 5649. -/
theorem bounds_15_5649 : exactInterval 15 5649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5649 : oddCount 5649 15 = 4 ∧ acceleratedOrbit 15 5649 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5649) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5649.1, data_15_5649.2]

/-- Complete interval computation for depth 15, residue 5650. -/
theorem bounds_15_5650 : exactInterval 15 5650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5650 : oddCount 5650 15 = 9 ∧ acceleratedOrbit 15 5650 = 3397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5650) = 3 ^ 9 * m + 3397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5650.1, data_15_5650.2]

/-- Complete interval computation for depth 15, residue 5651. -/
theorem bounds_15_5651 : exactInterval 15 5651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5651 : oddCount 5651 15 = 9 ∧ acceleratedOrbit 15 5651 = 3397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5651) = 3 ^ 9 * m + 3397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5651.1, data_15_5651.2]

/-- Complete interval computation for depth 15, residue 5652. -/
theorem bounds_15_5652 : exactInterval 15 5652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5652 : oddCount 5652 15 = 7 ∧ acceleratedOrbit 15 5652 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5652) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5652.1, data_15_5652.2]

/-- Complete interval computation for depth 15, residue 5653. -/
theorem bounds_15_5653 : exactInterval 15 5653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5653 : oddCount 5653 15 = 7 ∧ acceleratedOrbit 15 5653 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5653) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5653.1, data_15_5653.2]

/-- Complete interval computation for depth 15, residue 5654. -/
theorem bounds_15_5654 : exactInterval 15 5654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5654 : oddCount 5654 15 = 10 ∧ acceleratedOrbit 15 5654 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5654) = 3 ^ 10 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5654.1, data_15_5654.2]

/-- Complete interval computation for depth 15, residue 5655. -/
theorem bounds_15_5655 : exactInterval 15 5655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5655 : oddCount 5655 15 = 10 ∧ acceleratedOrbit 15 5655 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5655) = 3 ^ 10 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5655.1, data_15_5655.2]

/-- Complete interval computation for depth 15, residue 5656. -/
theorem bounds_15_5656 : exactInterval 15 5656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5656 : oddCount 5656 15 = 7 ∧ acceleratedOrbit 15 5656 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5656) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5656.1, data_15_5656.2]

/-- Complete interval computation for depth 15, residue 5657. -/
theorem bounds_15_5657 : exactInterval 15 5657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5657 : oddCount 5657 15 = 10 ∧ acceleratedOrbit 15 5657 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5657) = 3 ^ 10 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5657.1, data_15_5657.2]

/-- Complete interval computation for depth 15, residue 5658. -/
theorem bounds_15_5658 : exactInterval 15 5658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5658 : oddCount 5658 15 = 7 ∧ acceleratedOrbit 15 5658 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5658) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5658.1, data_15_5658.2]

/-- Complete interval computation for depth 15, residue 5659. -/
theorem bounds_15_5659 : exactInterval 15 5659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5659 : oddCount 5659 15 = 10 ∧ acceleratedOrbit 15 5659 = 10201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5659) = 3 ^ 10 * m + 10201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5659.1, data_15_5659.2]

/-- Complete interval computation for depth 15, residue 5660. -/
theorem bounds_15_5660 : exactInterval 15 5660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5660 : oddCount 5660 15 = 4 ∧ acceleratedOrbit 15 5660 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5660) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5660.1, data_15_5660.2]

/-- Complete interval computation for depth 15, residue 5661. -/
theorem bounds_15_5661 : exactInterval 15 5661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5661 : oddCount 5661 15 = 4 ∧ acceleratedOrbit 15 5661 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5661) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5661.1, data_15_5661.2]

/-- Complete interval computation for depth 15, residue 5662. -/
theorem bounds_15_5662 : exactInterval 15 5662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5662 : oddCount 5662 15 = 4 ∧ acceleratedOrbit 15 5662 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5662) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5662.1, data_15_5662.2]

/-- Complete interval computation for depth 15, residue 5663. -/
theorem bounds_15_5663 : exactInterval 15 5663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5663 : oddCount 5663 15 = 10 ∧ acceleratedOrbit 15 5663 = 10208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5663) = 3 ^ 10 * m + 10208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5663.1, data_15_5663.2]

/-- Complete interval computation for depth 15, residue 5664. -/
theorem bounds_15_5664 : exactInterval 15 5664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5664 : oddCount 5664 15 = 5 ∧ acceleratedOrbit 15 5664 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5664) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5664.1, data_15_5664.2]

/-- Complete interval computation for depth 15, residue 5665. -/
theorem bounds_15_5665 : exactInterval 15 5665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5665 : oddCount 5665 15 = 8 ∧ acceleratedOrbit 15 5665 = 1136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5665) = 3 ^ 8 * m + 1136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5665.1, data_15_5665.2]

/-- Complete interval computation for depth 15, residue 5666. -/
theorem bounds_15_5666 : exactInterval 15 5666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5666 : oddCount 5666 15 = 7 ∧ acceleratedOrbit 15 5666 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5666) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5666.1, data_15_5666.2]

/-- Complete interval computation for depth 15, residue 5667. -/
theorem bounds_15_5667 : exactInterval 15 5667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5667 : oddCount 5667 15 = 7 ∧ acceleratedOrbit 15 5667 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5667) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5667.1, data_15_5667.2]

end Collatz.Research.PassageAtlas.Batch0173
