import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0753

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24641. -/
theorem bounds_15_24641 : exactInterval 15 24641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24641 : oddCount 24641 15 = 8 ∧ acceleratedOrbit 15 24641 = 4936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24641) = 3 ^ 8 * m + 4936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24641.1, data_15_24641.2]

/-- Complete interval computation for depth 15, residue 24642. -/
theorem bounds_15_24642 : exactInterval 15 24642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24642 : oddCount 24642 15 = 8 ∧ acceleratedOrbit 15 24642 = 4936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24642) = 3 ^ 8 * m + 4936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24642.1, data_15_24642.2]

/-- Complete interval computation for depth 15, residue 24643. -/
theorem bounds_15_24643 : exactInterval 15 24643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24643 : oddCount 24643 15 = 8 ∧ acceleratedOrbit 15 24643 = 4936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24643) = 3 ^ 8 * m + 4936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24643.1, data_15_24643.2]

/-- Complete interval computation for depth 15, residue 24644. -/
theorem bounds_15_24644 : exactInterval 15 24644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24644 : oddCount 24644 15 = 4 ∧ acceleratedOrbit 15 24644 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24644) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24644.1, data_15_24644.2]

/-- Complete interval computation for depth 15, residue 24645. -/
theorem bounds_15_24645 : exactInterval 15 24645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24645 : oddCount 24645 15 = 4 ∧ acceleratedOrbit 15 24645 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24645) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24645.1, data_15_24645.2]

/-- Complete interval computation for depth 15, residue 24646. -/
theorem bounds_15_24646 : exactInterval 15 24646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24646 : oddCount 24646 15 = 4 ∧ acceleratedOrbit 15 24646 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24646) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24646.1, data_15_24646.2]

/-- Complete interval computation for depth 15, residue 24647. -/
theorem bounds_15_24647 : exactInterval 15 24647 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24647) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24647 : oddCount 24647 15 = 9 ∧ acceleratedOrbit 15 24647 = 14806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24647) = 3 ^ 9 * m + 14806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24647.1, data_15_24647.2]

/-- Complete interval computation for depth 15, residue 24648. -/
theorem bounds_15_24648 : exactInterval 15 24648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24648 : oddCount 24648 15 = 8 ∧ acceleratedOrbit 15 24648 = 4940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24648) = 3 ^ 8 * m + 4940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24648.1, data_15_24648.2]

/-- Complete interval computation for depth 15, residue 24649. -/
theorem bounds_15_24649 : exactInterval 15 24649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24649 : oddCount 24649 15 = 11 ∧ acceleratedOrbit 15 24649 = 133271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24649) = 3 ^ 11 * m + 133271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24649.1, data_15_24649.2]

/-- Complete interval computation for depth 15, residue 24650. -/
theorem bounds_15_24650 : exactInterval 15 24650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24650 : oddCount 24650 15 = 8 ∧ acceleratedOrbit 15 24650 = 4940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24650) = 3 ^ 8 * m + 4940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24650.1, data_15_24650.2]

/-- Complete interval computation for depth 15, residue 24651. -/
theorem bounds_15_24651 : exactInterval 15 24651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24651 : oddCount 24651 15 = 4 ∧ acceleratedOrbit 15 24651 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24651) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24651.1, data_15_24651.2]

/-- Complete interval computation for depth 15, residue 24652. -/
theorem bounds_15_24652 : exactInterval 15 24652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24652 : oddCount 24652 15 = 8 ∧ acceleratedOrbit 15 24652 = 4940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24652) = 3 ^ 8 * m + 4940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24652.1, data_15_24652.2]

/-- Complete interval computation for depth 15, residue 24653. -/
theorem bounds_15_24653 : exactInterval 15 24653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24653 : oddCount 24653 15 = 8 ∧ acceleratedOrbit 15 24653 = 4940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24653) = 3 ^ 8 * m + 4940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24653.1, data_15_24653.2]

/-- Complete interval computation for depth 15, residue 24654. -/
theorem bounds_15_24654 : exactInterval 15 24654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24654 : oddCount 24654 15 = 9 ∧ acceleratedOrbit 15 24654 = 14813 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24654) = 3 ^ 9 * m + 14813 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24654.1, data_15_24654.2]

/-- Complete interval computation for depth 15, residue 24655. -/
theorem bounds_15_24655 : exactInterval 15 24655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24655 : oddCount 24655 15 = 9 ∧ acceleratedOrbit 15 24655 = 14813 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24655) = 3 ^ 9 * m + 14813 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24655.1, data_15_24655.2]

/-- Complete interval computation for depth 15, residue 24656. -/
theorem bounds_15_24656 : exactInterval 15 24656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24656 : oddCount 24656 15 = 5 ∧ acceleratedOrbit 15 24656 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24656) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24656.1, data_15_24656.2]

/-- Complete interval computation for depth 15, residue 24657. -/
theorem bounds_15_24657 : exactInterval 15 24657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24657 : oddCount 24657 15 = 8 ∧ acceleratedOrbit 15 24657 = 4940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24657) = 3 ^ 8 * m + 4940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24657.1, data_15_24657.2]

/-- Complete interval computation for depth 15, residue 24658. -/
theorem bounds_15_24658 : exactInterval 15 24658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24658 : oddCount 24658 15 = 11 ∧ acceleratedOrbit 15 24658 = 133325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24658) = 3 ^ 11 * m + 133325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24658.1, data_15_24658.2]

/-- Complete interval computation for depth 15, residue 24659. -/
theorem bounds_15_24659 : exactInterval 15 24659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24659 : oddCount 24659 15 = 11 ∧ acceleratedOrbit 15 24659 = 133325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24659) = 3 ^ 11 * m + 133325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24659.1, data_15_24659.2]

/-- Complete interval computation for depth 15, residue 24660. -/
theorem bounds_15_24660 : exactInterval 15 24660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24660 : oddCount 24660 15 = 5 ∧ acceleratedOrbit 15 24660 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24660) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24660.1, data_15_24660.2]

/-- Complete interval computation for depth 15, residue 24661. -/
theorem bounds_15_24661 : exactInterval 15 24661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24661 : oddCount 24661 15 = 5 ∧ acceleratedOrbit 15 24661 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24661) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24661.1, data_15_24661.2]

/-- Complete interval computation for depth 15, residue 24662. -/
theorem bounds_15_24662 : exactInterval 15 24662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24662 : oddCount 24662 15 = 9 ∧ acceleratedOrbit 15 24662 = 14822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24662) = 3 ^ 9 * m + 14822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24662.1, data_15_24662.2]

/-- Complete interval computation for depth 15, residue 24663. -/
theorem bounds_15_24663 : exactInterval 15 24663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24663 : oddCount 24663 15 = 9 ∧ acceleratedOrbit 15 24663 = 14822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24663) = 3 ^ 9 * m + 14822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24663.1, data_15_24663.2]

/-- Complete interval computation for depth 15, residue 24664. -/
theorem bounds_15_24664 : exactInterval 15 24664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24664 : oddCount 24664 15 = 4 ∧ acceleratedOrbit 15 24664 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24664) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24664.1, data_15_24664.2]

/-- Complete interval computation for depth 15, residue 24665. -/
theorem bounds_15_24665 : exactInterval 15 24665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24665 : oddCount 24665 15 = 9 ∧ acceleratedOrbit 15 24665 = 14822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24665) = 3 ^ 9 * m + 14822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24665.1, data_15_24665.2]

/-- Complete interval computation for depth 15, residue 24666. -/
theorem bounds_15_24666 : exactInterval 15 24666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24666 : oddCount 24666 15 = 4 ∧ acceleratedOrbit 15 24666 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24666) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24666.1, data_15_24666.2]

/-- Complete interval computation for depth 15, residue 24667. -/
theorem bounds_15_24667 : exactInterval 15 24667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24667 : oddCount 24667 15 = 12 ∧ acceleratedOrbit 15 24667 = 400085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24667) = 3 ^ 12 * m + 400085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24667.1, data_15_24667.2]

/-- Complete interval computation for depth 15, residue 24668. -/
theorem bounds_15_24668 : exactInterval 15 24668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24668 : oddCount 24668 15 = 4 ∧ acceleratedOrbit 15 24668 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24668) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24668.1, data_15_24668.2]

/-- Complete interval computation for depth 15, residue 24669. -/
theorem bounds_15_24669 : exactInterval 15 24669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24669 : oddCount 24669 15 = 4 ∧ acceleratedOrbit 15 24669 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24669) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24669.1, data_15_24669.2]

/-- Complete interval computation for depth 15, residue 24670. -/
theorem bounds_15_24670 : exactInterval 15 24670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24670 : oddCount 24670 15 = 10 ∧ acceleratedOrbit 15 24670 = 44462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24670) = 3 ^ 10 * m + 44462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24670.1, data_15_24670.2]

/-- Complete interval computation for depth 15, residue 24671. -/
theorem bounds_15_24671 : exactInterval 15 24671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24671 : oddCount 24671 15 = 10 ∧ acceleratedOrbit 15 24671 = 44462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24671) = 3 ^ 10 * m + 44462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24671.1, data_15_24671.2]

/-- Complete interval computation for depth 15, residue 24672. -/
theorem bounds_15_24672 : exactInterval 15 24672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24672 : oddCount 24672 15 = 5 ∧ acceleratedOrbit 15 24672 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24672) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24672.1, data_15_24672.2]

/-- Complete interval computation for depth 15, residue 24673. -/
theorem bounds_15_24673 : exactInterval 15 24673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24673 : oddCount 24673 15 = 11 ∧ acceleratedOrbit 15 24673 = 133406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24673) = 3 ^ 11 * m + 133406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24673.1, data_15_24673.2]

end Collatz.Research.PassageAtlas.Batch0753
