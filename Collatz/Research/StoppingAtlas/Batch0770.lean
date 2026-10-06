import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0770

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4643. -/
theorem bounds_13_4643 : exactInterval 13 4643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4643 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4643) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4643 : oddCount 4643 13 = 4 ∧ acceleratedOrbit 13 4643 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4643 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4643) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4643.1, data_13_4643.2]

/-- Complete interval computation for depth 13, residue 4644. -/
theorem bounds_13_4644 : exactInterval 13 4644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4644 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4644) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4644 : oddCount 4644 13 = 9 ∧ acceleratedOrbit 13 4644 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4644 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4644) = 3 ^ 9 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4644.1, data_13_4644.2]

/-- Complete interval computation for depth 13, residue 4645. -/
theorem bounds_13_4645 : exactInterval 13 4645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4645 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4645) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4645 : oddCount 4645 13 = 9 ∧ acceleratedOrbit 13 4645 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4645 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4645) = 3 ^ 9 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4645.1, data_13_4645.2]

/-- Complete interval computation for depth 13, residue 4646. -/
theorem bounds_13_4646 : exactInterval 13 4646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4646 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4646) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4646 : oddCount 4646 13 = 9 ∧ acceleratedOrbit 13 4646 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4646 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4646) = 3 ^ 9 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4646.1, data_13_4646.2]

/-- Complete interval computation for depth 13, residue 4647. -/
theorem bounds_13_4647 : exactInterval 13 4647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4647 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4647) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4647 : oddCount 4647 13 = 8 ∧ acceleratedOrbit 13 4647 = 3725 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4647 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4647) = 3 ^ 8 * m + 3725 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4647.1, data_13_4647.2]

/-- Complete interval computation for depth 13, residue 4648. -/
theorem bounds_13_4648 : exactInterval 13 4648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4648 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4648) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4648 : oddCount 4648 13 = 4 ∧ acceleratedOrbit 13 4648 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4648 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4648) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4648.1, data_13_4648.2]

/-- Complete interval computation for depth 13, residue 4649. -/
theorem bounds_13_4649 : exactInterval 13 4649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4649 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4649) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4649 : oddCount 4649 13 = 10 ∧ acceleratedOrbit 13 4649 = 33524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4649 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4649) = 3 ^ 10 * m + 33524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4649.1, data_13_4649.2]

/-- Complete interval computation for depth 13, residue 4650. -/
theorem bounds_13_4650 : exactInterval 13 4650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4650 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4650) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4650 : oddCount 4650 13 = 4 ∧ acceleratedOrbit 13 4650 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4650 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4650) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4650.1, data_13_4650.2]

/-- Complete interval computation for depth 13, residue 4651. -/
theorem bounds_13_4651 : exactInterval 13 4651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4651 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4651) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4651 : oddCount 4651 13 = 4 ∧ acceleratedOrbit 13 4651 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4651 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4651) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4651.1, data_13_4651.2]

/-- Complete interval computation for depth 13, residue 4652. -/
theorem bounds_13_4652 : exactInterval 13 4652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4652 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4652) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4652 : oddCount 4652 13 = 6 ∧ acceleratedOrbit 13 4652 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4652 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4652) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4652.1, data_13_4652.2]

/-- Complete interval computation for depth 13, residue 4653. -/
theorem bounds_13_4653 : exactInterval 13 4653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4653 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4653) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4653 : oddCount 4653 13 = 6 ∧ acceleratedOrbit 13 4653 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4653 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4653) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4653.1, data_13_4653.2]

/-- Complete interval computation for depth 13, residue 4654. -/
theorem bounds_13_4654 : exactInterval 13 4654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4654 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4654) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4654 : oddCount 4654 13 = 6 ∧ acceleratedOrbit 13 4654 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4654 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4654) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4654.1, data_13_4654.2]

/-- Complete interval computation for depth 13, residue 4655. -/
theorem bounds_13_4655 : exactInterval 13 4655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4655 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4655) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4655 : oddCount 4655 13 = 9 ∧ acceleratedOrbit 13 4655 = 11188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4655 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4655) = 3 ^ 9 * m + 11188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4655.1, data_13_4655.2]

/-- Complete interval computation for depth 13, residue 4656. -/
theorem bounds_13_4656 : exactInterval 13 4656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4656 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4656) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4656 : oddCount 4656 13 = 4 ∧ acceleratedOrbit 13 4656 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4656 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4656) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4656.1, data_13_4656.2]

/-- Complete interval computation for depth 13, residue 4657. -/
theorem bounds_13_4657 : exactInterval 13 4657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4657 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4657) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4657 : oddCount 4657 13 = 6 ∧ acceleratedOrbit 13 4657 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4657 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4657) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4657.1, data_13_4657.2]

/-- Complete interval computation for depth 13, residue 4658. -/
theorem bounds_13_4658 : exactInterval 13 4658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4658 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4658) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4658 : oddCount 4658 13 = 6 ∧ acceleratedOrbit 13 4658 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4658 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4658) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4658.1, data_13_4658.2]

end Collatz.Research.StoppingAtlas.Batch0770
