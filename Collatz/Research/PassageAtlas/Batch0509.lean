import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0509

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16646. -/
theorem bounds_15_16646 : exactInterval 15 16646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16646 : oddCount 16646 15 = 6 ∧ acceleratedOrbit 15 16646 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16646) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16646.1, data_15_16646.2]

/-- Complete interval computation for depth 15, residue 16647. -/
theorem bounds_15_16647 : exactInterval 15 16647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16647 : oddCount 16647 15 = 9 ∧ acceleratedOrbit 15 16647 = 10001 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16647) = 3 ^ 9 * m + 10001 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16647.1, data_15_16647.2]

/-- Complete interval computation for depth 15, residue 16648. -/
theorem bounds_15_16648 : exactInterval 15 16648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16648 : oddCount 16648 15 = 6 ∧ acceleratedOrbit 15 16648 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16648) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16648.1, data_15_16648.2]

/-- Complete interval computation for depth 15, residue 16649. -/
theorem bounds_15_16649 : exactInterval 15 16649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16649 : oddCount 16649 15 = 9 ∧ acceleratedOrbit 15 16649 = 10003 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16649) = 3 ^ 9 * m + 10003 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16649.1, data_15_16649.2]

/-- Complete interval computation for depth 15, residue 16650. -/
theorem bounds_15_16650 : exactInterval 15 16650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16650 : oddCount 16650 15 = 6 ∧ acceleratedOrbit 15 16650 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16650) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16650.1, data_15_16650.2]

/-- Complete interval computation for depth 15, residue 16651. -/
theorem bounds_15_16651 : exactInterval 15 16651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16651 : oddCount 16651 15 = 6 ∧ acceleratedOrbit 15 16651 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16651) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16651.1, data_15_16651.2]

/-- Complete interval computation for depth 15, residue 16652. -/
theorem bounds_15_16652 : exactInterval 15 16652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16652 : oddCount 16652 15 = 6 ∧ acceleratedOrbit 15 16652 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16652) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16652.1, data_15_16652.2]

/-- Complete interval computation for depth 15, residue 16653. -/
theorem bounds_15_16653 : exactInterval 15 16653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16653 : oddCount 16653 15 = 6 ∧ acceleratedOrbit 15 16653 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16653) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16653.1, data_15_16653.2]

/-- Complete interval computation for depth 15, residue 16654. -/
theorem bounds_15_16654 : exactInterval 15 16654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16654 : oddCount 16654 15 = 7 ∧ acceleratedOrbit 15 16654 = 1112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16654) = 3 ^ 7 * m + 1112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16654.1, data_15_16654.2]

/-- Complete interval computation for depth 15, residue 16655. -/
theorem bounds_15_16655 : exactInterval 15 16655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16655 : oddCount 16655 15 = 7 ∧ acceleratedOrbit 15 16655 = 1112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16655) = 3 ^ 7 * m + 1112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16655.1, data_15_16655.2]

/-- Complete interval computation for depth 15, residue 16656. -/
theorem bounds_15_16656 : exactInterval 15 16656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16656 : oddCount 16656 15 = 5 ∧ acceleratedOrbit 15 16656 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16656) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16656.1, data_15_16656.2]

/-- Complete interval computation for depth 15, residue 16657. -/
theorem bounds_15_16657 : exactInterval 15 16657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16657 : oddCount 16657 15 = 6 ∧ acceleratedOrbit 15 16657 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16657) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16657.1, data_15_16657.2]

/-- Complete interval computation for depth 15, residue 16658. -/
theorem bounds_15_16658 : exactInterval 15 16658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16658 : oddCount 16658 15 = 10 ∧ acceleratedOrbit 15 16658 = 30026 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16658) = 3 ^ 10 * m + 30026 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16658.1, data_15_16658.2]

/-- Complete interval computation for depth 15, residue 16659. -/
theorem bounds_15_16659 : exactInterval 15 16659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16659 : oddCount 16659 15 = 10 ∧ acceleratedOrbit 15 16659 = 30026 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16659) = 3 ^ 10 * m + 30026 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16659.1, data_15_16659.2]

/-- Complete interval computation for depth 15, residue 16660. -/
theorem bounds_15_16660 : exactInterval 15 16660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16660 : oddCount 16660 15 = 5 ∧ acceleratedOrbit 15 16660 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16660) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16660.1, data_15_16660.2]

/-- Complete interval computation for depth 15, residue 16661. -/
theorem bounds_15_16661 : exactInterval 15 16661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16661 : oddCount 16661 15 = 5 ∧ acceleratedOrbit 15 16661 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16661) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16661.1, data_15_16661.2]

/-- Complete interval computation for depth 15, residue 16662. -/
theorem bounds_15_16662 : exactInterval 15 16662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16662 : oddCount 16662 15 = 8 ∧ acceleratedOrbit 15 16662 = 3338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16662) = 3 ^ 8 * m + 3338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16662.1, data_15_16662.2]

/-- Complete interval computation for depth 15, residue 16663. -/
theorem bounds_15_16663 : exactInterval 15 16663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16663 : oddCount 16663 15 = 8 ∧ acceleratedOrbit 15 16663 = 3338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16663) = 3 ^ 8 * m + 3338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16663.1, data_15_16663.2]

/-- Complete interval computation for depth 15, residue 16664. -/
theorem bounds_15_16664 : exactInterval 15 16664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16664 : oddCount 16664 15 = 5 ∧ acceleratedOrbit 15 16664 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16664) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16664.1, data_15_16664.2]

/-- Complete interval computation for depth 15, residue 16665. -/
theorem bounds_15_16665 : exactInterval 15 16665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16665 : oddCount 16665 15 = 8 ∧ acceleratedOrbit 15 16665 = 3338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16665) = 3 ^ 8 * m + 3338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16665.1, data_15_16665.2]

/-- Complete interval computation for depth 15, residue 16666. -/
theorem bounds_15_16666 : exactInterval 15 16666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16666 : oddCount 16666 15 = 5 ∧ acceleratedOrbit 15 16666 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16666) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16666.1, data_15_16666.2]

/-- Complete interval computation for depth 15, residue 16667. -/
theorem bounds_15_16667 : exactInterval 15 16667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16667 : oddCount 16667 15 = 11 ∧ acceleratedOrbit 15 16667 = 90112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16667) = 3 ^ 11 * m + 90112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16667.1, data_15_16667.2]

/-- Complete interval computation for depth 15, residue 16668. -/
theorem bounds_15_16668 : exactInterval 15 16668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16668 : oddCount 16668 15 = 10 ∧ acceleratedOrbit 15 16668 = 30050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16668) = 3 ^ 10 * m + 30050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16668.1, data_15_16668.2]

/-- Complete interval computation for depth 15, residue 16669. -/
theorem bounds_15_16669 : exactInterval 15 16669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16669 : oddCount 16669 15 = 10 ∧ acceleratedOrbit 15 16669 = 30050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16669) = 3 ^ 10 * m + 30050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16669.1, data_15_16669.2]

/-- Complete interval computation for depth 15, residue 16670. -/
theorem bounds_15_16670 : exactInterval 15 16670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16670 : oddCount 16670 15 = 10 ∧ acceleratedOrbit 15 16670 = 30050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16670) = 3 ^ 10 * m + 30050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16670.1, data_15_16670.2]

/-- Complete interval computation for depth 15, residue 16671. -/
theorem bounds_15_16671 : exactInterval 15 16671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16671 : oddCount 16671 15 = 9 ∧ acceleratedOrbit 15 16671 = 10016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16671) = 3 ^ 9 * m + 10016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16671.1, data_15_16671.2]

/-- Complete interval computation for depth 15, residue 16672. -/
theorem bounds_15_16672 : exactInterval 15 16672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16672 : oddCount 16672 15 = 5 ∧ acceleratedOrbit 15 16672 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16672) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16672.1, data_15_16672.2]

/-- Complete interval computation for depth 15, residue 16673. -/
theorem bounds_15_16673 : exactInterval 15 16673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16673 : oddCount 16673 15 = 8 ∧ acceleratedOrbit 15 16673 = 3341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16673) = 3 ^ 8 * m + 3341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16673.1, data_15_16673.2]

/-- Complete interval computation for depth 15, residue 16674. -/
theorem bounds_15_16674 : exactInterval 15 16674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16674 : oddCount 16674 15 = 8 ∧ acceleratedOrbit 15 16674 = 3341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16674) = 3 ^ 8 * m + 3341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16674.1, data_15_16674.2]

/-- Complete interval computation for depth 15, residue 16675. -/
theorem bounds_15_16675 : exactInterval 15 16675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16675 : oddCount 16675 15 = 8 ∧ acceleratedOrbit 15 16675 = 3341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16675) = 3 ^ 8 * m + 3341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16675.1, data_15_16675.2]

/-- Complete interval computation for depth 15, residue 16676. -/
theorem bounds_15_16676 : exactInterval 15 16676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16676 : oddCount 16676 15 = 8 ∧ acceleratedOrbit 15 16676 = 3341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16676) = 3 ^ 8 * m + 3341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16676.1, data_15_16676.2]

/-- Complete interval computation for depth 15, residue 16677. -/
theorem bounds_15_16677 : exactInterval 15 16677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16677 : oddCount 16677 15 = 8 ∧ acceleratedOrbit 15 16677 = 3341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16677) = 3 ^ 8 * m + 3341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16677.1, data_15_16677.2]

end Collatz.Research.PassageAtlas.Batch0509
