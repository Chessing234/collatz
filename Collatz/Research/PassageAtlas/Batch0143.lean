import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0143

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4653. -/
theorem bounds_15_4653 : exactInterval 15 4653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4653 : oddCount 4653 15 = 8 ∧ acceleratedOrbit 15 4653 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4653) = 3 ^ 8 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4653.1, data_15_4653.2]

/-- Complete interval computation for depth 15, residue 4654. -/
theorem bounds_15_4654 : exactInterval 15 4654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4654 : oddCount 4654 15 = 8 ∧ acceleratedOrbit 15 4654 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4654) = 3 ^ 8 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4654.1, data_15_4654.2]

/-- Complete interval computation for depth 15, residue 4655. -/
theorem bounds_15_4655 : exactInterval 15 4655 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4655) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4655 : oddCount 4655 15 = 9 ∧ acceleratedOrbit 15 4655 = 2797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4655) = 3 ^ 9 * m + 2797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4655.1, data_15_4655.2]

/-- Complete interval computation for depth 15, residue 4656. -/
theorem bounds_15_4656 : exactInterval 15 4656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4656 : oddCount 4656 15 = 6 ∧ acceleratedOrbit 15 4656 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4656) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4656.1, data_15_4656.2]

/-- Complete interval computation for depth 15, residue 4657. -/
theorem bounds_15_4657 : exactInterval 15 4657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4657 : oddCount 4657 15 = 8 ∧ acceleratedOrbit 15 4657 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4657) = 3 ^ 8 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4657.1, data_15_4657.2]

/-- Complete interval computation for depth 15, residue 4658. -/
theorem bounds_15_4658 : exactInterval 15 4658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4658 : oddCount 4658 15 = 8 ∧ acceleratedOrbit 15 4658 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4658) = 3 ^ 8 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4658.1, data_15_4658.2]

/-- Complete interval computation for depth 15, residue 4659. -/
theorem bounds_15_4659 : exactInterval 15 4659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4659 : oddCount 4659 15 = 8 ∧ acceleratedOrbit 15 4659 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4659) = 3 ^ 8 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4659.1, data_15_4659.2]

/-- Complete interval computation for depth 15, residue 4660. -/
theorem bounds_15_4660 : exactInterval 15 4660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4660 : oddCount 4660 15 = 6 ∧ acceleratedOrbit 15 4660 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4660) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4660.1, data_15_4660.2]

/-- Complete interval computation for depth 15, residue 4661. -/
theorem bounds_15_4661 : exactInterval 15 4661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4661 : oddCount 4661 15 = 6 ∧ acceleratedOrbit 15 4661 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4661) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4661.1, data_15_4661.2]

/-- Complete interval computation for depth 15, residue 4662. -/
theorem bounds_15_4662 : exactInterval 15 4662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4662 : oddCount 4662 15 = 8 ∧ acceleratedOrbit 15 4662 = 934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4662) = 3 ^ 8 * m + 934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4662.1, data_15_4662.2]

/-- Complete interval computation for depth 15, residue 4663. -/
theorem bounds_15_4663 : exactInterval 15 4663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4663 : oddCount 4663 15 = 8 ∧ acceleratedOrbit 15 4663 = 934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4663) = 3 ^ 8 * m + 934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4663.1, data_15_4663.2]

/-- Complete interval computation for depth 15, residue 4664. -/
theorem bounds_15_4664 : exactInterval 15 4664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4664 : oddCount 4664 15 = 6 ∧ acceleratedOrbit 15 4664 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4664) = 3 ^ 6 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4664.1, data_15_4664.2]

/-- Complete interval computation for depth 15, residue 4665. -/
theorem bounds_15_4665 : exactInterval 15 4665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4665 : oddCount 4665 15 = 10 ∧ acceleratedOrbit 15 4665 = 8414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4665) = 3 ^ 10 * m + 8414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4665.1, data_15_4665.2]

/-- Complete interval computation for depth 15, residue 4666. -/
theorem bounds_15_4666 : exactInterval 15 4666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4666 : oddCount 4666 15 = 6 ∧ acceleratedOrbit 15 4666 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4666) = 3 ^ 6 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4666.1, data_15_4666.2]

/-- Complete interval computation for depth 15, residue 4667. -/
theorem bounds_15_4667 : exactInterval 15 4667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4667 : oddCount 4667 15 = 6 ∧ acceleratedOrbit 15 4667 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4667) = 3 ^ 6 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4667.1, data_15_4667.2]

/-- Complete interval computation for depth 15, residue 4668. -/
theorem bounds_15_4668 : exactInterval 15 4668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4668 : oddCount 4668 15 = 6 ∧ acceleratedOrbit 15 4668 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4668) = 3 ^ 6 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4668.1, data_15_4668.2]

/-- Complete interval computation for depth 15, residue 4669. -/
theorem bounds_15_4669 : exactInterval 15 4669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4669 : oddCount 4669 15 = 6 ∧ acceleratedOrbit 15 4669 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4669) = 3 ^ 6 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4669.1, data_15_4669.2]

/-- Complete interval computation for depth 15, residue 4670. -/
theorem bounds_15_4670 : exactInterval 15 4670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4670 : oddCount 4670 15 = 10 ∧ acceleratedOrbit 15 4670 = 8423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4670) = 3 ^ 10 * m + 8423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4670.1, data_15_4670.2]

/-- Complete interval computation for depth 15, residue 4671. -/
theorem bounds_15_4671 : exactInterval 15 4671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4671 : oddCount 4671 15 = 10 ∧ acceleratedOrbit 15 4671 = 8423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4671) = 3 ^ 10 * m + 8423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4671.1, data_15_4671.2]

/-- Complete interval computation for depth 15, residue 4672. -/
theorem bounds_15_4672 : exactInterval 15 4672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4672 : oddCount 4672 15 = 6 ∧ acceleratedOrbit 15 4672 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4672) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4672.1, data_15_4672.2]

/-- Complete interval computation for depth 15, residue 4673. -/
theorem bounds_15_4673 : exactInterval 15 4673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4673 : oddCount 4673 15 = 7 ∧ acceleratedOrbit 15 4673 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4673) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4673.1, data_15_4673.2]

/-- Complete interval computation for depth 15, residue 4674. -/
theorem bounds_15_4674 : exactInterval 15 4674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4674 : oddCount 4674 15 = 7 ∧ acceleratedOrbit 15 4674 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4674) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4674.1, data_15_4674.2]

/-- Complete interval computation for depth 15, residue 4675. -/
theorem bounds_15_4675 : exactInterval 15 4675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4675 : oddCount 4675 15 = 7 ∧ acceleratedOrbit 15 4675 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4675) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4675.1, data_15_4675.2]

/-- Complete interval computation for depth 15, residue 4676. -/
theorem bounds_15_4676 : exactInterval 15 4676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4676 : oddCount 4676 15 = 7 ∧ acceleratedOrbit 15 4676 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4676) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4676.1, data_15_4676.2]

/-- Complete interval computation for depth 15, residue 4677. -/
theorem bounds_15_4677 : exactInterval 15 4677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4677 : oddCount 4677 15 = 7 ∧ acceleratedOrbit 15 4677 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4677) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4677.1, data_15_4677.2]

/-- Complete interval computation for depth 15, residue 4678. -/
theorem bounds_15_4678 : exactInterval 15 4678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4678 : oddCount 4678 15 = 7 ∧ acceleratedOrbit 15 4678 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4678) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4678.1, data_15_4678.2]

/-- Complete interval computation for depth 15, residue 4679. -/
theorem bounds_15_4679 : exactInterval 15 4679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4679 : oddCount 4679 15 = 8 ∧ acceleratedOrbit 15 4679 = 938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4679) = 3 ^ 8 * m + 938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4679.1, data_15_4679.2]

/-- Complete interval computation for depth 15, residue 4680. -/
theorem bounds_15_4680 : exactInterval 15 4680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4680 : oddCount 4680 15 = 7 ∧ acceleratedOrbit 15 4680 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4680) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4680.1, data_15_4680.2]

/-- Complete interval computation for depth 15, residue 4681. -/
theorem bounds_15_4681 : exactInterval 15 4681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4681 : oddCount 4681 15 = 8 ∧ acceleratedOrbit 15 4681 = 938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4681) = 3 ^ 8 * m + 938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4681.1, data_15_4681.2]

/-- Complete interval computation for depth 15, residue 4682. -/
theorem bounds_15_4682 : exactInterval 15 4682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4682 : oddCount 4682 15 = 7 ∧ acceleratedOrbit 15 4682 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4682) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4682.1, data_15_4682.2]

/-- Complete interval computation for depth 15, residue 4683. -/
theorem bounds_15_4683 : exactInterval 15 4683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4683 : oddCount 4683 15 = 7 ∧ acceleratedOrbit 15 4683 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4683) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4683.1, data_15_4683.2]

/-- Complete interval computation for depth 15, residue 4684. -/
theorem bounds_15_4684 : exactInterval 15 4684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4684 : oddCount 4684 15 = 7 ∧ acceleratedOrbit 15 4684 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4684) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4684.1, data_15_4684.2]

end Collatz.Research.PassageAtlas.Batch0143
