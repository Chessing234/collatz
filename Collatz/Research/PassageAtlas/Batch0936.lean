import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0936

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30638. -/
theorem bounds_15_30638 : exactInterval 15 30638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30638 : oddCount 30638 15 = 9 ∧ acceleratedOrbit 15 30638 = 18407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30638) = 3 ^ 9 * m + 18407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30638.1, data_15_30638.2]

/-- Complete interval computation for depth 15, residue 30639. -/
theorem bounds_15_30639 : exactInterval 15 30639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30639 : oddCount 30639 15 = 9 ∧ acceleratedOrbit 15 30639 = 18407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30639) = 3 ^ 9 * m + 18407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30639.1, data_15_30639.2]

/-- Complete interval computation for depth 15, residue 30640. -/
theorem bounds_15_30640 : exactInterval 15 30640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30640 : oddCount 30640 15 = 7 ∧ acceleratedOrbit 15 30640 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30640) = 3 ^ 7 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30640.1, data_15_30640.2]

/-- Complete interval computation for depth 15, residue 30641. -/
theorem bounds_15_30641 : exactInterval 15 30641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30641 : oddCount 30641 15 = 4 ∧ acceleratedOrbit 15 30641 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30641) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30641.1, data_15_30641.2]

/-- Complete interval computation for depth 15, residue 30642. -/
theorem bounds_15_30642 : exactInterval 15 30642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30642 : oddCount 30642 15 = 4 ∧ acceleratedOrbit 15 30642 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30642) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30642.1, data_15_30642.2]

/-- Complete interval computation for depth 15, residue 30643. -/
theorem bounds_15_30643 : exactInterval 15 30643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30643 : oddCount 30643 15 = 4 ∧ acceleratedOrbit 15 30643 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30643) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30643.1, data_15_30643.2]

/-- Complete interval computation for depth 15, residue 30644. -/
theorem bounds_15_30644 : exactInterval 15 30644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30644 : oddCount 30644 15 = 7 ∧ acceleratedOrbit 15 30644 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30644) = 3 ^ 7 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30644.1, data_15_30644.2]

/-- Complete interval computation for depth 15, residue 30645. -/
theorem bounds_15_30645 : exactInterval 15 30645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30645 : oddCount 30645 15 = 7 ∧ acceleratedOrbit 15 30645 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30645) = 3 ^ 7 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30645.1, data_15_30645.2]

/-- Complete interval computation for depth 15, residue 30646. -/
theorem bounds_15_30646 : exactInterval 15 30646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30646 : oddCount 30646 15 = 9 ∧ acceleratedOrbit 15 30646 = 18413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30646) = 3 ^ 9 * m + 18413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30646.1, data_15_30646.2]

/-- Complete interval computation for depth 15, residue 30647. -/
theorem bounds_15_30647 : exactInterval 15 30647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30647 : oddCount 30647 15 = 9 ∧ acceleratedOrbit 15 30647 = 18413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30647) = 3 ^ 9 * m + 18413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30647.1, data_15_30647.2]

/-- Complete interval computation for depth 15, residue 30648. -/
theorem bounds_15_30648 : exactInterval 15 30648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30648 : oddCount 30648 15 = 7 ∧ acceleratedOrbit 15 30648 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30648) = 3 ^ 7 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30648.1, data_15_30648.2]

/-- Complete interval computation for depth 15, residue 30649. -/
theorem bounds_15_30649 : exactInterval 15 30649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30649 : oddCount 30649 15 = 6 ∧ acceleratedOrbit 15 30649 = 682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30649) = 3 ^ 6 * m + 682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30649.1, data_15_30649.2]

/-- Complete interval computation for depth 15, residue 30650. -/
theorem bounds_15_30650 : exactInterval 15 30650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30650 : oddCount 30650 15 = 7 ∧ acceleratedOrbit 15 30650 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30650) = 3 ^ 7 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30650.1, data_15_30650.2]

/-- Complete interval computation for depth 15, residue 30651. -/
theorem bounds_15_30651 : exactInterval 15 30651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30651 : oddCount 30651 15 = 6 ∧ acceleratedOrbit 15 30651 = 682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30651) = 3 ^ 6 * m + 682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30651.1, data_15_30651.2]

/-- Complete interval computation for depth 15, residue 30652. -/
theorem bounds_15_30652 : exactInterval 15 30652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30652 : oddCount 30652 15 = 9 ∧ acceleratedOrbit 15 30652 = 18415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30652) = 3 ^ 9 * m + 18415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30652.1, data_15_30652.2]

/-- Complete interval computation for depth 15, residue 30653. -/
theorem bounds_15_30653 : exactInterval 15 30653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30653 : oddCount 30653 15 = 9 ∧ acceleratedOrbit 15 30653 = 18415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30653) = 3 ^ 9 * m + 18415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30653.1, data_15_30653.2]

/-- Complete interval computation for depth 15, residue 30654. -/
theorem bounds_15_30654 : exactInterval 15 30654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30654 : oddCount 30654 15 = 9 ∧ acceleratedOrbit 15 30654 = 18415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30654) = 3 ^ 9 * m + 18415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30654.1, data_15_30654.2]

/-- Complete interval computation for depth 15, residue 30655. -/
theorem bounds_15_30655 : exactInterval 15 30655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30655 : oddCount 30655 15 = 10 ∧ acceleratedOrbit 15 30655 = 55244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30655) = 3 ^ 10 * m + 55244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30655.1, data_15_30655.2]

/-- Complete interval computation for depth 15, residue 30656. -/
theorem bounds_15_30656 : exactInterval 15 30656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30656 : oddCount 30656 15 = 7 ∧ acceleratedOrbit 15 30656 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30656) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30656.1, data_15_30656.2]

/-- Complete interval computation for depth 15, residue 30657. -/
theorem bounds_15_30657 : exactInterval 15 30657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30657 : oddCount 30657 15 = 7 ∧ acceleratedOrbit 15 30657 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30657) = 3 ^ 7 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30657.1, data_15_30657.2]

/-- Complete interval computation for depth 15, residue 30658. -/
theorem bounds_15_30658 : exactInterval 15 30658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30658 : oddCount 30658 15 = 8 ∧ acceleratedOrbit 15 30658 = 6140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30658) = 3 ^ 8 * m + 6140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30658.1, data_15_30658.2]

/-- Complete interval computation for depth 15, residue 30659. -/
theorem bounds_15_30659 : exactInterval 15 30659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30659 : oddCount 30659 15 = 8 ∧ acceleratedOrbit 15 30659 = 6140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30659) = 3 ^ 8 * m + 6140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30659.1, data_15_30659.2]

/-- Complete interval computation for depth 15, residue 30660. -/
theorem bounds_15_30660 : exactInterval 15 30660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30660 : oddCount 30660 15 = 7 ∧ acceleratedOrbit 15 30660 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30660) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30660.1, data_15_30660.2]

/-- Complete interval computation for depth 15, residue 30661. -/
theorem bounds_15_30661 : exactInterval 15 30661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30661 : oddCount 30661 15 = 7 ∧ acceleratedOrbit 15 30661 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30661) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30661.1, data_15_30661.2]

/-- Complete interval computation for depth 15, residue 30662. -/
theorem bounds_15_30662 : exactInterval 15 30662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30662 : oddCount 30662 15 = 7 ∧ acceleratedOrbit 15 30662 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30662) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30662.1, data_15_30662.2]

/-- Complete interval computation for depth 15, residue 30663. -/
theorem bounds_15_30663 : exactInterval 15 30663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30663 : oddCount 30663 15 = 8 ∧ acceleratedOrbit 15 30663 = 6140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30663) = 3 ^ 8 * m + 6140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30663.1, data_15_30663.2]

/-- Complete interval computation for depth 15, residue 30664. -/
theorem bounds_15_30664 : exactInterval 15 30664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30664 : oddCount 30664 15 = 6 ∧ acceleratedOrbit 15 30664 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30664) = 3 ^ 6 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30664.1, data_15_30664.2]

/-- Complete interval computation for depth 15, residue 30665. -/
theorem bounds_15_30665 : exactInterval 15 30665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30665 : oddCount 30665 15 = 10 ∧ acceleratedOrbit 15 30665 = 55268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30665) = 3 ^ 10 * m + 55268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30665.1, data_15_30665.2]

/-- Complete interval computation for depth 15, residue 30666. -/
theorem bounds_15_30666 : exactInterval 15 30666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30666 : oddCount 30666 15 = 6 ∧ acceleratedOrbit 15 30666 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30666) = 3 ^ 6 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30666.1, data_15_30666.2]

/-- Complete interval computation for depth 15, residue 30667. -/
theorem bounds_15_30667 : exactInterval 15 30667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30667 : oddCount 30667 15 = 6 ∧ acceleratedOrbit 15 30667 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30667) = 3 ^ 6 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30667.1, data_15_30667.2]

/-- Complete interval computation for depth 15, residue 30668. -/
theorem bounds_15_30668 : exactInterval 15 30668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30668 : oddCount 30668 15 = 6 ∧ acceleratedOrbit 15 30668 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30668) = 3 ^ 6 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30668.1, data_15_30668.2]

/-- Complete interval computation for depth 15, residue 30669. -/
theorem bounds_15_30669 : exactInterval 15 30669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30669 : oddCount 30669 15 = 6 ∧ acceleratedOrbit 15 30669 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30669) = 3 ^ 6 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30669.1, data_15_30669.2]

end Collatz.Research.PassageAtlas.Batch0936
