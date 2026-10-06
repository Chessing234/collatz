import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0570

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18644. -/
theorem bounds_15_18644 : exactInterval 15 18644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18644 : oddCount 18644 15 = 4 ∧ acceleratedOrbit 15 18644 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18644) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18644.1, data_15_18644.2]

/-- Complete interval computation for depth 15, residue 18645. -/
theorem bounds_15_18645 : exactInterval 15 18645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18645 : oddCount 18645 15 = 4 ∧ acceleratedOrbit 15 18645 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18645) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18645.1, data_15_18645.2]

/-- Complete interval computation for depth 15, residue 18646. -/
theorem bounds_15_18646 : exactInterval 15 18646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18646 : oddCount 18646 15 = 9 ∧ acceleratedOrbit 15 18646 = 11204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18646) = 3 ^ 9 * m + 11204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18646.1, data_15_18646.2]

/-- Complete interval computation for depth 15, residue 18647. -/
theorem bounds_15_18647 : exactInterval 15 18647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18647 : oddCount 18647 15 = 9 ∧ acceleratedOrbit 15 18647 = 11204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18647) = 3 ^ 9 * m + 11204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18647.1, data_15_18647.2]

/-- Complete interval computation for depth 15, residue 18648. -/
theorem bounds_15_18648 : exactInterval 15 18648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18648 : oddCount 18648 15 = 8 ∧ acceleratedOrbit 15 18648 = 3736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18648) = 3 ^ 8 * m + 3736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18648.1, data_15_18648.2]

/-- Complete interval computation for depth 15, residue 18649. -/
theorem bounds_15_18649 : exactInterval 15 18649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18649 : oddCount 18649 15 = 8 ∧ acceleratedOrbit 15 18649 = 3736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18649) = 3 ^ 8 * m + 3736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18649.1, data_15_18649.2]

/-- Complete interval computation for depth 15, residue 18650. -/
theorem bounds_15_18650 : exactInterval 15 18650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18650 : oddCount 18650 15 = 8 ∧ acceleratedOrbit 15 18650 = 3736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18650) = 3 ^ 8 * m + 3736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18650.1, data_15_18650.2]

/-- Complete interval computation for depth 15, residue 18651. -/
theorem bounds_15_18651 : exactInterval 15 18651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18651 : oddCount 18651 15 = 11 ∧ acceleratedOrbit 15 18651 = 100844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18651) = 3 ^ 11 * m + 100844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18651.1, data_15_18651.2]

/-- Complete interval computation for depth 15, residue 18652. -/
theorem bounds_15_18652 : exactInterval 15 18652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18652 : oddCount 18652 15 = 8 ∧ acceleratedOrbit 15 18652 = 3736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18652) = 3 ^ 8 * m + 3736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18652.1, data_15_18652.2]

/-- Complete interval computation for depth 15, residue 18653. -/
theorem bounds_15_18653 : exactInterval 15 18653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18653 : oddCount 18653 15 = 8 ∧ acceleratedOrbit 15 18653 = 3736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18653) = 3 ^ 8 * m + 3736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18653.1, data_15_18653.2]

/-- Complete interval computation for depth 15, residue 18654. -/
theorem bounds_15_18654 : exactInterval 15 18654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18654 : oddCount 18654 15 = 9 ∧ acceleratedOrbit 15 18654 = 11207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18654) = 3 ^ 9 * m + 11207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18654.1, data_15_18654.2]

/-- Complete interval computation for depth 15, residue 18655. -/
theorem bounds_15_18655 : exactInterval 15 18655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18655 : oddCount 18655 15 = 9 ∧ acceleratedOrbit 15 18655 = 11207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18655) = 3 ^ 9 * m + 11207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18655.1, data_15_18655.2]

/-- Complete interval computation for depth 15, residue 18656. -/
theorem bounds_15_18656 : exactInterval 15 18656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18656 : oddCount 18656 15 = 6 ∧ acceleratedOrbit 15 18656 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18656) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18656.1, data_15_18656.2]

/-- Complete interval computation for depth 15, residue 18657. -/
theorem bounds_15_18657 : exactInterval 15 18657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18657 : oddCount 18657 15 = 10 ∧ acceleratedOrbit 15 18657 = 33625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18657) = 3 ^ 10 * m + 33625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18657.1, data_15_18657.2]

/-- Complete interval computation for depth 15, residue 18658. -/
theorem bounds_15_18658 : exactInterval 15 18658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18658 : oddCount 18658 15 = 4 ∧ acceleratedOrbit 15 18658 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18658) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18658.1, data_15_18658.2]

/-- Complete interval computation for depth 15, residue 18659. -/
theorem bounds_15_18659 : exactInterval 15 18659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18659 : oddCount 18659 15 = 4 ∧ acceleratedOrbit 15 18659 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18659) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18659.1, data_15_18659.2]

/-- Complete interval computation for depth 15, residue 18660. -/
theorem bounds_15_18660 : exactInterval 15 18660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18660 : oddCount 18660 15 = 8 ∧ acceleratedOrbit 15 18660 = 3739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18660) = 3 ^ 8 * m + 3739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18660.1, data_15_18660.2]

/-- Complete interval computation for depth 15, residue 18661. -/
theorem bounds_15_18661 : exactInterval 15 18661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18661 : oddCount 18661 15 = 8 ∧ acceleratedOrbit 15 18661 = 3739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18661) = 3 ^ 8 * m + 3739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18661.1, data_15_18661.2]

/-- Complete interval computation for depth 15, residue 18662. -/
theorem bounds_15_18662 : exactInterval 15 18662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18662 : oddCount 18662 15 = 8 ∧ acceleratedOrbit 15 18662 = 3739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18662) = 3 ^ 8 * m + 3739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18662.1, data_15_18662.2]

/-- Complete interval computation for depth 15, residue 18663. -/
theorem bounds_15_18663 : exactInterval 15 18663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18663 : oddCount 18663 15 = 10 ∧ acceleratedOrbit 15 18663 = 33635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18663) = 3 ^ 10 * m + 33635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18663.1, data_15_18663.2]

/-- Complete interval computation for depth 15, residue 18664. -/
theorem bounds_15_18664 : exactInterval 15 18664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18664 : oddCount 18664 15 = 6 ∧ acceleratedOrbit 15 18664 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18664) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18664.1, data_15_18664.2]

/-- Complete interval computation for depth 15, residue 18665. -/
theorem bounds_15_18665 : exactInterval 15 18665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18665 : oddCount 18665 15 = 10 ∧ acceleratedOrbit 15 18665 = 33641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18665) = 3 ^ 10 * m + 33641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18665.1, data_15_18665.2]

/-- Complete interval computation for depth 15, residue 18666. -/
theorem bounds_15_18666 : exactInterval 15 18666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18666 : oddCount 18666 15 = 6 ∧ acceleratedOrbit 15 18666 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18666) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18666.1, data_15_18666.2]

/-- Complete interval computation for depth 15, residue 18667. -/
theorem bounds_15_18667 : exactInterval 15 18667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18667 : oddCount 18667 15 = 7 ∧ acceleratedOrbit 15 18667 = 1246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18667) = 3 ^ 7 * m + 1246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18667.1, data_15_18667.2]

/-- Complete interval computation for depth 15, residue 18668. -/
theorem bounds_15_18668 : exactInterval 15 18668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18668 : oddCount 18668 15 = 6 ∧ acceleratedOrbit 15 18668 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18668) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18668.1, data_15_18668.2]

/-- Complete interval computation for depth 15, residue 18669. -/
theorem bounds_15_18669 : exactInterval 15 18669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18669 : oddCount 18669 15 = 6 ∧ acceleratedOrbit 15 18669 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18669) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18669.1, data_15_18669.2]

/-- Complete interval computation for depth 15, residue 18670. -/
theorem bounds_15_18670 : exactInterval 15 18670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18670 : oddCount 18670 15 = 6 ∧ acceleratedOrbit 15 18670 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18670) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18670.1, data_15_18670.2]

/-- Complete interval computation for depth 15, residue 18671. -/
theorem bounds_15_18671 : exactInterval 15 18671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18671 : oddCount 18671 15 = 13 ∧ acceleratedOrbit 15 18671 = 908495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18671) = 3 ^ 13 * m + 908495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18671.1, data_15_18671.2]

/-- Complete interval computation for depth 15, residue 18672. -/
theorem bounds_15_18672 : exactInterval 15 18672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18672 : oddCount 18672 15 = 6 ∧ acceleratedOrbit 15 18672 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18672) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18672.1, data_15_18672.2]

/-- Complete interval computation for depth 15, residue 18673. -/
theorem bounds_15_18673 : exactInterval 15 18673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18673 : oddCount 18673 15 = 6 ∧ acceleratedOrbit 15 18673 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18673) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18673.1, data_15_18673.2]

/-- Complete interval computation for depth 15, residue 18674. -/
theorem bounds_15_18674 : exactInterval 15 18674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18674 : oddCount 18674 15 = 8 ∧ acceleratedOrbit 15 18674 = 3740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18674) = 3 ^ 8 * m + 3740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18674.1, data_15_18674.2]

/-- Complete interval computation for depth 15, residue 18675. -/
theorem bounds_15_18675 : exactInterval 15 18675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18675 : oddCount 18675 15 = 8 ∧ acceleratedOrbit 15 18675 = 3740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18675) = 3 ^ 8 * m + 3740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18675.1, data_15_18675.2]

/-- Complete interval computation for depth 15, residue 18676. -/
theorem bounds_15_18676 : exactInterval 15 18676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18676 : oddCount 18676 15 = 6 ∧ acceleratedOrbit 15 18676 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18676) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18676.1, data_15_18676.2]

end Collatz.Research.PassageAtlas.Batch0570
