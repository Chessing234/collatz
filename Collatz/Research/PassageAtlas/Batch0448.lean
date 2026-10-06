import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0448

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14647. -/
theorem bounds_15_14647 : exactInterval 15 14647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14647 : oddCount 14647 15 = 10 ∧ acceleratedOrbit 15 14647 = 26399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14647) = 3 ^ 10 * m + 26399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14647.1, data_15_14647.2]

/-- Complete interval computation for depth 15, residue 14648. -/
theorem bounds_15_14648 : exactInterval 15 14648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14648 : oddCount 14648 15 = 8 ∧ acceleratedOrbit 15 14648 = 2936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14648) = 3 ^ 8 * m + 2936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14648.1, data_15_14648.2]

/-- Complete interval computation for depth 15, residue 14649. -/
theorem bounds_15_14649 : exactInterval 15 14649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14649 : oddCount 14649 15 = 10 ∧ acceleratedOrbit 15 14649 = 26405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14649) = 3 ^ 10 * m + 26405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14649.1, data_15_14649.2]

/-- Complete interval computation for depth 15, residue 14650. -/
theorem bounds_15_14650 : exactInterval 15 14650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14650 : oddCount 14650 15 = 8 ∧ acceleratedOrbit 15 14650 = 2936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14650) = 3 ^ 8 * m + 2936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14650.1, data_15_14650.2]

/-- Complete interval computation for depth 15, residue 14651. -/
theorem bounds_15_14651 : exactInterval 15 14651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14651 : oddCount 14651 15 = 8 ∧ acceleratedOrbit 15 14651 = 2936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14651) = 3 ^ 8 * m + 2936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14651.1, data_15_14651.2]

/-- Complete interval computation for depth 15, residue 14652. -/
theorem bounds_15_14652 : exactInterval 15 14652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14652 : oddCount 14652 15 = 8 ∧ acceleratedOrbit 15 14652 = 2936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14652) = 3 ^ 8 * m + 2936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14652.1, data_15_14652.2]

/-- Complete interval computation for depth 15, residue 14653. -/
theorem bounds_15_14653 : exactInterval 15 14653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14653 : oddCount 14653 15 = 8 ∧ acceleratedOrbit 15 14653 = 2936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14653) = 3 ^ 8 * m + 2936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14653.1, data_15_14653.2]

/-- Complete interval computation for depth 15, residue 14654. -/
theorem bounds_15_14654 : exactInterval 15 14654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14654 : oddCount 14654 15 = 10 ∧ acceleratedOrbit 15 14654 = 26411 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14654) = 3 ^ 10 * m + 26411 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14654.1, data_15_14654.2]

/-- Complete interval computation for depth 15, residue 14655. -/
theorem bounds_15_14655 : exactInterval 15 14655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14655 : oddCount 14655 15 = 10 ∧ acceleratedOrbit 15 14655 = 26411 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14655) = 3 ^ 10 * m + 26411 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14655.1, data_15_14655.2]

/-- Complete interval computation for depth 15, residue 14656. -/
theorem bounds_15_14656 : exactInterval 15 14656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14656 : oddCount 14656 15 = 4 ∧ acceleratedOrbit 15 14656 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14656) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14656.1, data_15_14656.2]

/-- Complete interval computation for depth 15, residue 14657. -/
theorem bounds_15_14657 : exactInterval 15 14657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14657 : oddCount 14657 15 = 5 ∧ acceleratedOrbit 15 14657 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14657) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14657.1, data_15_14657.2]

/-- Complete interval computation for depth 15, residue 14658. -/
theorem bounds_15_14658 : exactInterval 15 14658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14658 : oddCount 14658 15 = 10 ∧ acceleratedOrbit 15 14658 = 26426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14658) = 3 ^ 10 * m + 26426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14658.1, data_15_14658.2]

/-- Complete interval computation for depth 15, residue 14659. -/
theorem bounds_15_14659 : exactInterval 15 14659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14659 : oddCount 14659 15 = 10 ∧ acceleratedOrbit 15 14659 = 26426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14659) = 3 ^ 10 * m + 26426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14659.1, data_15_14659.2]

/-- Complete interval computation for depth 15, residue 14660. -/
theorem bounds_15_14660 : exactInterval 15 14660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14660 : oddCount 14660 15 = 7 ∧ acceleratedOrbit 15 14660 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14660) = 3 ^ 7 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14660.1, data_15_14660.2]

/-- Complete interval computation for depth 15, residue 14661. -/
theorem bounds_15_14661 : exactInterval 15 14661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14661 : oddCount 14661 15 = 7 ∧ acceleratedOrbit 15 14661 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14661) = 3 ^ 7 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14661.1, data_15_14661.2]

/-- Complete interval computation for depth 15, residue 14662. -/
theorem bounds_15_14662 : exactInterval 15 14662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14662 : oddCount 14662 15 = 7 ∧ acceleratedOrbit 15 14662 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14662) = 3 ^ 7 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14662.1, data_15_14662.2]

/-- Complete interval computation for depth 15, residue 14663. -/
theorem bounds_15_14663 : exactInterval 15 14663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14663 : oddCount 14663 15 = 12 ∧ acceleratedOrbit 15 14663 = 237836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14663) = 3 ^ 12 * m + 237836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14663.1, data_15_14663.2]

/-- Complete interval computation for depth 15, residue 14664. -/
theorem bounds_15_14664 : exactInterval 15 14664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14664 : oddCount 14664 15 = 7 ∧ acceleratedOrbit 15 14664 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14664) = 3 ^ 7 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14664.1, data_15_14664.2]

/-- Complete interval computation for depth 15, residue 14665. -/
theorem bounds_15_14665 : exactInterval 15 14665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14665 : oddCount 14665 15 = 7 ∧ acceleratedOrbit 15 14665 = 979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14665) = 3 ^ 7 * m + 979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14665.1, data_15_14665.2]

/-- Complete interval computation for depth 15, residue 14666. -/
theorem bounds_15_14666 : exactInterval 15 14666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14666 : oddCount 14666 15 = 7 ∧ acceleratedOrbit 15 14666 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14666) = 3 ^ 7 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14666.1, data_15_14666.2]

/-- Complete interval computation for depth 15, residue 14667. -/
theorem bounds_15_14667 : exactInterval 15 14667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14667 : oddCount 14667 15 = 7 ∧ acceleratedOrbit 15 14667 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14667) = 3 ^ 7 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14667.1, data_15_14667.2]

/-- Complete interval computation for depth 15, residue 14668. -/
theorem bounds_15_14668 : exactInterval 15 14668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14668 : oddCount 14668 15 = 7 ∧ acceleratedOrbit 15 14668 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14668) = 3 ^ 7 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14668.1, data_15_14668.2]

/-- Complete interval computation for depth 15, residue 14669. -/
theorem bounds_15_14669 : exactInterval 15 14669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14669 : oddCount 14669 15 = 7 ∧ acceleratedOrbit 15 14669 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14669) = 3 ^ 7 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14669.1, data_15_14669.2]

/-- Complete interval computation for depth 15, residue 14670. -/
theorem bounds_15_14670 : exactInterval 15 14670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14670 : oddCount 14670 15 = 11 ∧ acceleratedOrbit 15 14670 = 79325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14670) = 3 ^ 11 * m + 79325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14670.1, data_15_14670.2]

/-- Complete interval computation for depth 15, residue 14671. -/
theorem bounds_15_14671 : exactInterval 15 14671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14671 : oddCount 14671 15 = 11 ∧ acceleratedOrbit 15 14671 = 79325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14671) = 3 ^ 11 * m + 79325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14671.1, data_15_14671.2]

/-- Complete interval computation for depth 15, residue 14672. -/
theorem bounds_15_14672 : exactInterval 15 14672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14672 : oddCount 14672 15 = 4 ∧ acceleratedOrbit 15 14672 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14672) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14672.1, data_15_14672.2]

/-- Complete interval computation for depth 15, residue 14673. -/
theorem bounds_15_14673 : exactInterval 15 14673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14673 : oddCount 14673 15 = 10 ∧ acceleratedOrbit 15 14673 = 26450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14673) = 3 ^ 10 * m + 26450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14673.1, data_15_14673.2]

/-- Complete interval computation for depth 15, residue 14674. -/
theorem bounds_15_14674 : exactInterval 15 14674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14674 : oddCount 14674 15 = 10 ∧ acceleratedOrbit 15 14674 = 26450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14674) = 3 ^ 10 * m + 26450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14674.1, data_15_14674.2]

/-- Complete interval computation for depth 15, residue 14675. -/
theorem bounds_15_14675 : exactInterval 15 14675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14675 : oddCount 14675 15 = 10 ∧ acceleratedOrbit 15 14675 = 26450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14675) = 3 ^ 10 * m + 26450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14675.1, data_15_14675.2]

/-- Complete interval computation for depth 15, residue 14676. -/
theorem bounds_15_14676 : exactInterval 15 14676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14676 : oddCount 14676 15 = 4 ∧ acceleratedOrbit 15 14676 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14676) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14676.1, data_15_14676.2]

/-- Complete interval computation for depth 15, residue 14677. -/
theorem bounds_15_14677 : exactInterval 15 14677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14677 : oddCount 14677 15 = 4 ∧ acceleratedOrbit 15 14677 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14677) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14677.1, data_15_14677.2]

/-- Complete interval computation for depth 15, residue 14678. -/
theorem bounds_15_14678 : exactInterval 15 14678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14678 : oddCount 14678 15 = 8 ∧ acceleratedOrbit 15 14678 = 2942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14678) = 3 ^ 8 * m + 2942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14678.1, data_15_14678.2]

/-- Complete interval computation for depth 15, residue 14679. -/
theorem bounds_15_14679 : exactInterval 15 14679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14679 : oddCount 14679 15 = 8 ∧ acceleratedOrbit 15 14679 = 2942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14679) = 3 ^ 8 * m + 2942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14679.1, data_15_14679.2]

end Collatz.Research.PassageAtlas.Batch0448
