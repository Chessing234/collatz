import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0662

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21659. -/
theorem bounds_15_21659 : exactInterval 15 21659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21659 : oddCount 21659 15 = 8 ∧ acceleratedOrbit 15 21659 = 4337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21659) = 3 ^ 8 * m + 4337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21659.1, data_15_21659.2]

/-- Complete interval computation for depth 15, residue 21660. -/
theorem bounds_15_21660 : exactInterval 15 21660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21660 : oddCount 21660 15 = 6 ∧ acceleratedOrbit 15 21660 = 482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21660) = 3 ^ 6 * m + 482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21660.1, data_15_21660.2]

/-- Complete interval computation for depth 15, residue 21661. -/
theorem bounds_15_21661 : exactInterval 15 21661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21661 : oddCount 21661 15 = 6 ∧ acceleratedOrbit 15 21661 = 482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21661) = 3 ^ 6 * m + 482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21661.1, data_15_21661.2]

/-- Complete interval computation for depth 15, residue 21662. -/
theorem bounds_15_21662 : exactInterval 15 21662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21662 : oddCount 21662 15 = 6 ∧ acceleratedOrbit 15 21662 = 482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21662) = 3 ^ 6 * m + 482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21662.1, data_15_21662.2]

/-- Complete interval computation for depth 15, residue 21663. -/
theorem bounds_15_21663 : exactInterval 15 21663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21663 : oddCount 21663 15 = 11 ∧ acceleratedOrbit 15 21663 = 117119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21663) = 3 ^ 11 * m + 117119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21663.1, data_15_21663.2]

/-- Complete interval computation for depth 15, residue 21664. -/
theorem bounds_15_21664 : exactInterval 15 21664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21664 : oddCount 21664 15 = 7 ∧ acceleratedOrbit 15 21664 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21664) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21664.1, data_15_21664.2]

/-- Complete interval computation for depth 15, residue 21665. -/
theorem bounds_15_21665 : exactInterval 15 21665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21665 : oddCount 21665 15 = 9 ∧ acceleratedOrbit 15 21665 = 13016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21665) = 3 ^ 9 * m + 13016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21665.1, data_15_21665.2]

/-- Complete interval computation for depth 15, residue 21666. -/
theorem bounds_15_21666 : exactInterval 15 21666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21666 : oddCount 21666 15 = 8 ∧ acceleratedOrbit 15 21666 = 4340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21666) = 3 ^ 8 * m + 4340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21666.1, data_15_21666.2]

/-- Complete interval computation for depth 15, residue 21667. -/
theorem bounds_15_21667 : exactInterval 15 21667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21667 : oddCount 21667 15 = 8 ∧ acceleratedOrbit 15 21667 = 4340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21667) = 3 ^ 8 * m + 4340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21667.1, data_15_21667.2]

/-- Complete interval computation for depth 15, residue 21668. -/
theorem bounds_15_21668 : exactInterval 15 21668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21668 : oddCount 21668 15 = 8 ∧ acceleratedOrbit 15 21668 = 4340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21668) = 3 ^ 8 * m + 4340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21668.1, data_15_21668.2]

/-- Complete interval computation for depth 15, residue 21669. -/
theorem bounds_15_21669 : exactInterval 15 21669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21669 : oddCount 21669 15 = 8 ∧ acceleratedOrbit 15 21669 = 4340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21669) = 3 ^ 8 * m + 4340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21669.1, data_15_21669.2]

/-- Complete interval computation for depth 15, residue 21670. -/
theorem bounds_15_21670 : exactInterval 15 21670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21670 : oddCount 21670 15 = 8 ∧ acceleratedOrbit 15 21670 = 4340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21670) = 3 ^ 8 * m + 4340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21670.1, data_15_21670.2]

/-- Complete interval computation for depth 15, residue 21671. -/
theorem bounds_15_21671 : exactInterval 15 21671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21671 : oddCount 21671 15 = 10 ∧ acceleratedOrbit 15 21671 = 39055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21671) = 3 ^ 10 * m + 39055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21671.1, data_15_21671.2]

/-- Complete interval computation for depth 15, residue 21672. -/
theorem bounds_15_21672 : exactInterval 15 21672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21672 : oddCount 21672 15 = 7 ∧ acceleratedOrbit 15 21672 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21672) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21672.1, data_15_21672.2]

/-- Complete interval computation for depth 15, residue 21673. -/
theorem bounds_15_21673 : exactInterval 15 21673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21673 : oddCount 21673 15 = 10 ∧ acceleratedOrbit 15 21673 = 39059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21673) = 3 ^ 10 * m + 39059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21673.1, data_15_21673.2]

/-- Complete interval computation for depth 15, residue 21674. -/
theorem bounds_15_21674 : exactInterval 15 21674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21674 : oddCount 21674 15 = 7 ∧ acceleratedOrbit 15 21674 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21674) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21674.1, data_15_21674.2]

/-- Complete interval computation for depth 15, residue 21675. -/
theorem bounds_15_21675 : exactInterval 15 21675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21675 : oddCount 21675 15 = 7 ∧ acceleratedOrbit 15 21675 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21675) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21675.1, data_15_21675.2]

/-- Complete interval computation for depth 15, residue 21676. -/
theorem bounds_15_21676 : exactInterval 15 21676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21676 : oddCount 21676 15 = 7 ∧ acceleratedOrbit 15 21676 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21676) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21676.1, data_15_21676.2]

/-- Complete interval computation for depth 15, residue 21677. -/
theorem bounds_15_21677 : exactInterval 15 21677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21677 : oddCount 21677 15 = 7 ∧ acceleratedOrbit 15 21677 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21677) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21677.1, data_15_21677.2]

/-- Complete interval computation for depth 15, residue 21678. -/
theorem bounds_15_21678 : exactInterval 15 21678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21678 : oddCount 21678 15 = 7 ∧ acceleratedOrbit 15 21678 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21678) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21678.1, data_15_21678.2]

/-- Complete interval computation for depth 15, residue 21679. -/
theorem bounds_15_21679 : exactInterval 15 21679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21679 : oddCount 21679 15 = 7 ∧ acceleratedOrbit 15 21679 = 1447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21679) = 3 ^ 7 * m + 1447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21679.1, data_15_21679.2]

/-- Complete interval computation for depth 15, residue 21680. -/
theorem bounds_15_21680 : exactInterval 15 21680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21680 : oddCount 21680 15 = 6 ∧ acceleratedOrbit 15 21680 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21680) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21680.1, data_15_21680.2]

/-- Complete interval computation for depth 15, residue 21681. -/
theorem bounds_15_21681 : exactInterval 15 21681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21681 : oddCount 21681 15 = 9 ∧ acceleratedOrbit 15 21681 = 13031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21681) = 3 ^ 9 * m + 13031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21681.1, data_15_21681.2]

/-- Complete interval computation for depth 15, residue 21682. -/
theorem bounds_15_21682 : exactInterval 15 21682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21682 : oddCount 21682 15 = 9 ∧ acceleratedOrbit 15 21682 = 13031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21682) = 3 ^ 9 * m + 13031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21682.1, data_15_21682.2]

/-- Complete interval computation for depth 15, residue 21683. -/
theorem bounds_15_21683 : exactInterval 15 21683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21683 : oddCount 21683 15 = 9 ∧ acceleratedOrbit 15 21683 = 13031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21683) = 3 ^ 9 * m + 13031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21683.1, data_15_21683.2]

/-- Complete interval computation for depth 15, residue 21684. -/
theorem bounds_15_21684 : exactInterval 15 21684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21684 : oddCount 21684 15 = 6 ∧ acceleratedOrbit 15 21684 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21684) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21684.1, data_15_21684.2]

/-- Complete interval computation for depth 15, residue 21685. -/
theorem bounds_15_21685 : exactInterval 15 21685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21685 : oddCount 21685 15 = 6 ∧ acceleratedOrbit 15 21685 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21685) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21685.1, data_15_21685.2]

/-- Complete interval computation for depth 15, residue 21686. -/
theorem bounds_15_21686 : exactInterval 15 21686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21686 : oddCount 21686 15 = 10 ∧ acceleratedOrbit 15 21686 = 39086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21686) = 3 ^ 10 * m + 39086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21686.1, data_15_21686.2]

/-- Complete interval computation for depth 15, residue 21687. -/
theorem bounds_15_21687 : exactInterval 15 21687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21687 : oddCount 21687 15 = 10 ∧ acceleratedOrbit 15 21687 = 39086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21687) = 3 ^ 10 * m + 39086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21687.1, data_15_21687.2]

/-- Complete interval computation for depth 15, residue 21688. -/
theorem bounds_15_21688 : exactInterval 15 21688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21688 : oddCount 21688 15 = 6 ∧ acceleratedOrbit 15 21688 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21688) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21688.1, data_15_21688.2]

/-- Complete interval computation for depth 15, residue 21689. -/
theorem bounds_15_21689 : exactInterval 15 21689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21689 : oddCount 21689 15 = 9 ∧ acceleratedOrbit 15 21689 = 13031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21689) = 3 ^ 9 * m + 13031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21689.1, data_15_21689.2]

/-- Complete interval computation for depth 15, residue 21690. -/
theorem bounds_15_21690 : exactInterval 15 21690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21690 : oddCount 21690 15 = 6 ∧ acceleratedOrbit 15 21690 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21690) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21690.1, data_15_21690.2]

/-- Complete interval computation for depth 15, residue 21691. -/
theorem bounds_15_21691 : exactInterval 15 21691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21691 : oddCount 21691 15 = 11 ∧ acceleratedOrbit 15 21691 = 117278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21691) = 3 ^ 11 * m + 117278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21691.1, data_15_21691.2]

end Collatz.Research.PassageAtlas.Batch0662
