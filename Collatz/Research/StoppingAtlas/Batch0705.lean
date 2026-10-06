import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0705

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3645. -/
theorem bounds_13_3645 : exactInterval 13 3645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3645 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3645) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3645 : oddCount 3645 13 = 6 ∧ acceleratedOrbit 13 3645 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3645 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3645) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3645.1, data_13_3645.2]

/-- Complete interval computation for depth 13, residue 3646. -/
theorem bounds_13_3646 : exactInterval 13 3646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3646 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3646) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3646 : oddCount 3646 13 = 7 ∧ acceleratedOrbit 13 3646 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3646 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3646) = 3 ^ 7 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3646.1, data_13_3646.2]

/-- Complete interval computation for depth 13, residue 3647. -/
theorem bounds_13_3647 : exactInterval 13 3647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3647 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3647) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3647 : oddCount 3647 13 = 7 ∧ acceleratedOrbit 13 3647 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3647 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3647) = 3 ^ 7 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3647.1, data_13_3647.2]

/-- Complete interval computation for depth 13, residue 3648. -/
theorem bounds_13_3648 : exactInterval 13 3648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3648 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3648) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3648 : oddCount 3648 13 = 4 ∧ acceleratedOrbit 13 3648 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3648 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3648) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3648.1, data_13_3648.2]

/-- Complete interval computation for depth 13, residue 3649. -/
theorem bounds_13_3649 : exactInterval 13 3649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3649 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3649) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3649 : oddCount 3649 13 = 6 ∧ acceleratedOrbit 13 3649 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3649 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3649) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3649.1, data_13_3649.2]

/-- Complete interval computation for depth 13, residue 3650. -/
theorem bounds_13_3650 : exactInterval 13 3650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3650 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3650) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3650 : oddCount 3650 13 = 6 ∧ acceleratedOrbit 13 3650 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3650 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3650) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3650.1, data_13_3650.2]

/-- Complete interval computation for depth 13, residue 3651. -/
theorem bounds_13_3651 : exactInterval 13 3651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3651 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3651) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3651 : oddCount 3651 13 = 6 ∧ acceleratedOrbit 13 3651 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3651 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3651) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3651.1, data_13_3651.2]

/-- Complete interval computation for depth 13, residue 3652. -/
theorem bounds_13_3652 : exactInterval 13 3652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3652 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3652) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3652 : oddCount 3652 13 = 5 ∧ acceleratedOrbit 13 3652 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3652 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3652) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3652.1, data_13_3652.2]

/-- Complete interval computation for depth 13, residue 3653. -/
theorem bounds_13_3653 : exactInterval 13 3653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3653 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3653) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3653 : oddCount 3653 13 = 5 ∧ acceleratedOrbit 13 3653 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3653 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3653) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3653.1, data_13_3653.2]

/-- Complete interval computation for depth 13, residue 3654. -/
theorem bounds_13_3654 : exactInterval 13 3654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3654 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3654) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3654 : oddCount 3654 13 = 5 ∧ acceleratedOrbit 13 3654 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3654 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3654) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3654.1, data_13_3654.2]

/-- Complete interval computation for depth 13, residue 3655. -/
theorem bounds_13_3655 : exactInterval 13 3655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3655 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3655) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3655 : oddCount 3655 13 = 8 ∧ acceleratedOrbit 13 3655 = 2929 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3655 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3655) = 3 ^ 8 * m + 2929 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3655.1, data_13_3655.2]

/-- Complete interval computation for depth 13, residue 3656. -/
theorem bounds_13_3656 : exactInterval 13 3656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3656 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3656) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3656 : oddCount 3656 13 = 5 ∧ acceleratedOrbit 13 3656 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3656 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3656) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3656.1, data_13_3656.2]

/-- Complete interval computation for depth 13, residue 3657. -/
theorem bounds_13_3657 : exactInterval 13 3657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3657 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3657) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3657 : oddCount 3657 13 = 7 ∧ acceleratedOrbit 13 3657 = 977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3657 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3657) = 3 ^ 7 * m + 977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3657.1, data_13_3657.2]

/-- Complete interval computation for depth 13, residue 3658. -/
theorem bounds_13_3658 : exactInterval 13 3658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3658 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3658) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3658 : oddCount 3658 13 = 5 ∧ acceleratedOrbit 13 3658 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3658 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3658) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3658.1, data_13_3658.2]

/-- Complete interval computation for depth 13, residue 3659. -/
theorem bounds_13_3659 : exactInterval 13 3659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3659 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3659) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3659 : oddCount 3659 13 = 5 ∧ acceleratedOrbit 13 3659 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3659 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3659) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3659.1, data_13_3659.2]

end Collatz.Research.StoppingAtlas.Batch0705
