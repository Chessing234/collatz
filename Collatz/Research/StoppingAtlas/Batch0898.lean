import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0898

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6609. -/
theorem bounds_13_6609 : exactInterval 13 6609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6609 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6609) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6609 : oddCount 6609 13 = 6 ∧ acceleratedOrbit 13 6609 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6609 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6609) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6609.1, data_13_6609.2]

/-- Complete interval computation for depth 13, residue 6610. -/
theorem bounds_13_6610 : exactInterval 13 6610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6610 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6610) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6610 : oddCount 6610 13 = 7 ∧ acceleratedOrbit 13 6610 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6610 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6610) = 3 ^ 7 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6610.1, data_13_6610.2]

/-- Complete interval computation for depth 13, residue 6611. -/
theorem bounds_13_6611 : exactInterval 13 6611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6611 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6611) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6611 : oddCount 6611 13 = 7 ∧ acceleratedOrbit 13 6611 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6611 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6611) = 3 ^ 7 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6611.1, data_13_6611.2]

/-- Complete interval computation for depth 13, residue 6612. -/
theorem bounds_13_6612 : exactInterval 13 6612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6612 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6612) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6612 : oddCount 6612 13 = 6 ∧ acceleratedOrbit 13 6612 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6612 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6612) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6612.1, data_13_6612.2]

/-- Complete interval computation for depth 13, residue 6613. -/
theorem bounds_13_6613 : exactInterval 13 6613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6613 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6613) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6613 : oddCount 6613 13 = 6 ∧ acceleratedOrbit 13 6613 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6613 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6613) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6613.1, data_13_6613.2]

/-- Complete interval computation for depth 13, residue 6614. -/
theorem bounds_13_6614 : exactInterval 13 6614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6614 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6614) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6614 : oddCount 6614 13 = 9 ∧ acceleratedOrbit 13 6614 = 15902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6614 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6614) = 3 ^ 9 * m + 15902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6614.1, data_13_6614.2]

/-- Complete interval computation for depth 13, residue 6615. -/
theorem bounds_13_6615 : exactInterval 13 6615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6615 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6615) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6615 : oddCount 6615 13 = 9 ∧ acceleratedOrbit 13 6615 = 15902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6615 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6615) = 3 ^ 9 * m + 15902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6615.1, data_13_6615.2]

/-- Complete interval computation for depth 13, residue 6616. -/
theorem bounds_13_6616 : exactInterval 13 6616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6616 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6616) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6616 : oddCount 6616 13 = 5 ∧ acceleratedOrbit 13 6616 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6616 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6616) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6616.1, data_13_6616.2]

/-- Complete interval computation for depth 13, residue 6617. -/
theorem bounds_13_6617 : exactInterval 13 6617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6617 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6617) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6617 : oddCount 6617 13 = 5 ∧ acceleratedOrbit 13 6617 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6617 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6617) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6617.1, data_13_6617.2]

/-- Complete interval computation for depth 13, residue 6618. -/
theorem bounds_13_6618 : exactInterval 13 6618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6618 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6618) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6618 : oddCount 6618 13 = 5 ∧ acceleratedOrbit 13 6618 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6618 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6618) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6618.1, data_13_6618.2]

/-- Complete interval computation for depth 13, residue 6619. -/
theorem bounds_13_6619 : exactInterval 13 6619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6619 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6619) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6619 : oddCount 6619 13 = 7 ∧ acceleratedOrbit 13 6619 = 1768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6619 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6619) = 3 ^ 7 * m + 1768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6619.1, data_13_6619.2]

/-- Complete interval computation for depth 13, residue 6620. -/
theorem bounds_13_6620 : exactInterval 13 6620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6620 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6620) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6620 : oddCount 6620 13 = 5 ∧ acceleratedOrbit 13 6620 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6620 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6620) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6620.1, data_13_6620.2]

/-- Complete interval computation for depth 13, residue 6621. -/
theorem bounds_13_6621 : exactInterval 13 6621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6621 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6621) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6621 : oddCount 6621 13 = 5 ∧ acceleratedOrbit 13 6621 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6621 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6621) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6621.1, data_13_6621.2]

/-- Complete interval computation for depth 13, residue 6622. -/
theorem bounds_13_6622 : exactInterval 13 6622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6622 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6622) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6622 : oddCount 6622 13 = 10 ∧ acceleratedOrbit 13 6622 = 47749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6622 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6622) = 3 ^ 10 * m + 47749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6622.1, data_13_6622.2]

/-- Complete interval computation for depth 13, residue 6623. -/
theorem bounds_13_6623 : exactInterval 13 6623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6623 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6623) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6623 : oddCount 6623 13 = 10 ∧ acceleratedOrbit 13 6623 = 47749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6623 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6623) = 3 ^ 10 * m + 47749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6623.1, data_13_6623.2]

/-- Complete interval computation for depth 13, residue 6624. -/
theorem bounds_13_6624 : exactInterval 13 6624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6624 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6624) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6624 : oddCount 6624 13 = 6 ∧ acceleratedOrbit 13 6624 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6624 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6624) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6624.1, data_13_6624.2]

end Collatz.Research.StoppingAtlas.Batch0898
