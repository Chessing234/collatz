import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0902

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6671. -/
theorem bounds_13_6671 : exactInterval 13 6671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6671 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6671) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6671 : oddCount 6671 13 = 9 ∧ acceleratedOrbit 13 6671 = 16037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6671 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6671) = 3 ^ 9 * m + 16037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6671.1, data_13_6671.2]

/-- Complete interval computation for depth 13, residue 6672. -/
theorem bounds_13_6672 : exactInterval 13 6672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6672 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6672) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6672 : oddCount 6672 13 = 5 ∧ acceleratedOrbit 13 6672 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6672 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6672) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6672.1, data_13_6672.2]

/-- Complete interval computation for depth 13, residue 6673. -/
theorem bounds_13_6673 : exactInterval 13 6673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6673 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6673) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6673 : oddCount 6673 13 = 3 ∧ acceleratedOrbit 13 6673 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6673 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6673) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6673.1, data_13_6673.2]

/-- Complete interval computation for depth 13, residue 6674. -/
theorem bounds_13_6674 : exactInterval 13 6674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6674 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6674) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6674 : oddCount 6674 13 = 7 ∧ acceleratedOrbit 13 6674 = 1783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6674 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6674) = 3 ^ 7 * m + 1783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6674.1, data_13_6674.2]

/-- Complete interval computation for depth 13, residue 6675. -/
theorem bounds_13_6675 : exactInterval 13 6675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6675 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6675) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6675 : oddCount 6675 13 = 7 ∧ acceleratedOrbit 13 6675 = 1783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6675 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6675) = 3 ^ 7 * m + 1783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6675.1, data_13_6675.2]

/-- Complete interval computation for depth 13, residue 6676. -/
theorem bounds_13_6676 : exactInterval 13 6676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6676 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6676) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6676 : oddCount 6676 13 = 5 ∧ acceleratedOrbit 13 6676 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6676 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6676) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6676.1, data_13_6676.2]

/-- Complete interval computation for depth 13, residue 6677. -/
theorem bounds_13_6677 : exactInterval 13 6677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6677 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6677) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6677 : oddCount 6677 13 = 5 ∧ acceleratedOrbit 13 6677 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6677 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6677) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6677.1, data_13_6677.2]

/-- Complete interval computation for depth 13, residue 6678. -/
theorem bounds_13_6678 : exactInterval 13 6678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6678 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6678) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6678 : oddCount 6678 13 = 6 ∧ acceleratedOrbit 13 6678 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6678 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6678) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6678.1, data_13_6678.2]

/-- Complete interval computation for depth 13, residue 6679. -/
theorem bounds_13_6679 : exactInterval 13 6679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6679 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6679) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6679 : oddCount 6679 13 = 6 ∧ acceleratedOrbit 13 6679 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6679 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6679) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6679.1, data_13_6679.2]

/-- Complete interval computation for depth 13, residue 6680. -/
theorem bounds_13_6680 : exactInterval 13 6680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6680 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6680) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6680 : oddCount 6680 13 = 5 ∧ acceleratedOrbit 13 6680 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6680 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6680) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6680.1, data_13_6680.2]

/-- Complete interval computation for depth 13, residue 6681. -/
theorem bounds_13_6681 : exactInterval 13 6681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6681 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6681) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6681 : oddCount 6681 13 = 6 ∧ acceleratedOrbit 13 6681 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6681 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6681) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6681.1, data_13_6681.2]

/-- Complete interval computation for depth 13, residue 6682. -/
theorem bounds_13_6682 : exactInterval 13 6682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6682 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6682) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6682 : oddCount 6682 13 = 5 ∧ acceleratedOrbit 13 6682 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6682 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6682) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6682.1, data_13_6682.2]

/-- Complete interval computation for depth 13, residue 6683. -/
theorem bounds_13_6683 : exactInterval 13 6683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6683 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6683) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6683 : oddCount 6683 13 = 8 ∧ acceleratedOrbit 13 6683 = 5354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6683 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6683) = 3 ^ 8 * m + 5354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6683.1, data_13_6683.2]

/-- Complete interval computation for depth 13, residue 6684. -/
theorem bounds_13_6684 : exactInterval 13 6684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6684 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6684) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6684 : oddCount 6684 13 = 6 ∧ acceleratedOrbit 13 6684 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6684 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6684) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6684.1, data_13_6684.2]

/-- Complete interval computation for depth 13, residue 6685. -/
theorem bounds_13_6685 : exactInterval 13 6685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6685 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6685) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6685 : oddCount 6685 13 = 6 ∧ acceleratedOrbit 13 6685 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6685 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6685) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6685.1, data_13_6685.2]

end Collatz.Research.StoppingAtlas.Batch0902
