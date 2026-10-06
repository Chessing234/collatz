import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0903

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6686. -/
theorem bounds_13_6686 : exactInterval 13 6686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6686 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6686) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6686 : oddCount 6686 13 = 6 ∧ acceleratedOrbit 13 6686 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6686 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6686) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6686.1, data_13_6686.2]

/-- Complete interval computation for depth 13, residue 6687. -/
theorem bounds_13_6687 : exactInterval 13 6687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6687 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6687) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6687 : oddCount 6687 13 = 8 ∧ acceleratedOrbit 13 6687 = 5357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6687 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6687) = 3 ^ 8 * m + 5357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6687.1, data_13_6687.2]

/-- Complete interval computation for depth 13, residue 6688. -/
theorem bounds_13_6688 : exactInterval 13 6688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6688 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6688) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6688 : oddCount 6688 13 = 4 ∧ acceleratedOrbit 13 6688 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6688 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6688) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6688.1, data_13_6688.2]

/-- Complete interval computation for depth 13, residue 6689. -/
theorem bounds_13_6689 : exactInterval 13 6689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6689 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6689) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6689 : oddCount 6689 13 = 6 ∧ acceleratedOrbit 13 6689 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6689 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6689) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6689.1, data_13_6689.2]

/-- Complete interval computation for depth 13, residue 6690. -/
theorem bounds_13_6690 : exactInterval 13 6690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6690 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6690) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6690 : oddCount 6690 13 = 5 ∧ acceleratedOrbit 13 6690 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6690 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6690) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6690.1, data_13_6690.2]

/-- Complete interval computation for depth 13, residue 6691. -/
theorem bounds_13_6691 : exactInterval 13 6691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6691 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6691) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6691 : oddCount 6691 13 = 5 ∧ acceleratedOrbit 13 6691 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6691 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6691) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6691.1, data_13_6691.2]

/-- Complete interval computation for depth 13, residue 6692. -/
theorem bounds_13_6692 : exactInterval 13 6692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6692 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6692) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6692 : oddCount 6692 13 = 8 ∧ acceleratedOrbit 13 6692 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6692 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6692) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6692.1, data_13_6692.2]

/-- Complete interval computation for depth 13, residue 6693. -/
theorem bounds_13_6693 : exactInterval 13 6693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6693 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6693) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6693 : oddCount 6693 13 = 8 ∧ acceleratedOrbit 13 6693 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6693 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6693) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6693.1, data_13_6693.2]

/-- Complete interval computation for depth 13, residue 6694. -/
theorem bounds_13_6694 : exactInterval 13 6694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6694 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6694) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6694 : oddCount 6694 13 = 8 ∧ acceleratedOrbit 13 6694 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6694 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6694) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6694.1, data_13_6694.2]

/-- Complete interval computation for depth 13, residue 6695. -/
theorem bounds_13_6695 : exactInterval 13 6695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6695 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6695) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6695 : oddCount 6695 13 = 6 ∧ acceleratedOrbit 13 6695 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6695 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6695) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6695.1, data_13_6695.2]

/-- Complete interval computation for depth 13, residue 6696. -/
theorem bounds_13_6696 : exactInterval 13 6696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6696 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6696) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6696 : oddCount 6696 13 = 4 ∧ acceleratedOrbit 13 6696 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6696 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6696) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6696.1, data_13_6696.2]

/-- Complete interval computation for depth 13, residue 6697. -/
theorem bounds_13_6697 : exactInterval 13 6697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6697 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6697) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6697 : oddCount 6697 13 = 8 ∧ acceleratedOrbit 13 6697 = 5365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6697 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6697) = 3 ^ 8 * m + 5365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6697.1, data_13_6697.2]

/-- Complete interval computation for depth 13, residue 6698. -/
theorem bounds_13_6698 : exactInterval 13 6698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6698 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6698) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6698 : oddCount 6698 13 = 4 ∧ acceleratedOrbit 13 6698 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6698 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6698) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6698.1, data_13_6698.2]

/-- Complete interval computation for depth 13, residue 6699. -/
theorem bounds_13_6699 : exactInterval 13 6699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6699 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6699) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6699 : oddCount 6699 13 = 5 ∧ acceleratedOrbit 13 6699 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6699 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6699) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6699.1, data_13_6699.2]

/-- Complete interval computation for depth 13, residue 6700. -/
theorem bounds_13_6700 : exactInterval 13 6700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6700 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6700) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6700 : oddCount 6700 13 = 5 ∧ acceleratedOrbit 13 6700 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6700 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6700) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6700.1, data_13_6700.2]

/-- Complete interval computation for depth 13, residue 6701. -/
theorem bounds_13_6701 : exactInterval 13 6701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6701 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6701) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6701 : oddCount 6701 13 = 5 ∧ acceleratedOrbit 13 6701 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6701 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6701) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6701.1, data_13_6701.2]

end Collatz.Research.StoppingAtlas.Batch0903
