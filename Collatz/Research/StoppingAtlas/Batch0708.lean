import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0708

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3691. -/
theorem bounds_13_3691 : exactInterval 13 3691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3691 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3691) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3691 : oddCount 3691 13 = 7 ∧ acceleratedOrbit 13 3691 = 986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3691 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3691) = 3 ^ 7 * m + 986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3691.1, data_13_3691.2]

/-- Complete interval computation for depth 13, residue 3692. -/
theorem bounds_13_3692 : exactInterval 13 3692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3692 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3692) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3692 : oddCount 3692 13 = 6 ∧ acceleratedOrbit 13 3692 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3692 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3692) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3692.1, data_13_3692.2]

/-- Complete interval computation for depth 13, residue 3693. -/
theorem bounds_13_3693 : exactInterval 13 3693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3693 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3693) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3693 : oddCount 3693 13 = 6 ∧ acceleratedOrbit 13 3693 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3693 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3693) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3693.1, data_13_3693.2]

/-- Complete interval computation for depth 13, residue 3694. -/
theorem bounds_13_3694 : exactInterval 13 3694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3694 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3694) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3694 : oddCount 3694 13 = 6 ∧ acceleratedOrbit 13 3694 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3694 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3694) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3694.1, data_13_3694.2]

/-- Complete interval computation for depth 13, residue 3695. -/
theorem bounds_13_3695 : exactInterval 13 3695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3695 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3695) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3695 : oddCount 3695 13 = 9 ∧ acceleratedOrbit 13 3695 = 8882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3695 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3695) = 3 ^ 9 * m + 8882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3695.1, data_13_3695.2]

/-- Complete interval computation for depth 13, residue 3696. -/
theorem bounds_13_3696 : exactInterval 13 3696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3696 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3696) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3696 : oddCount 3696 13 = 7 ∧ acceleratedOrbit 13 3696 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3696 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3696) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3696.1, data_13_3696.2]

/-- Complete interval computation for depth 13, residue 3697. -/
theorem bounds_13_3697 : exactInterval 13 3697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3697 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3697) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3697 : oddCount 3697 13 = 4 ∧ acceleratedOrbit 13 3697 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3697 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3697) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3697.1, data_13_3697.2]

/-- Complete interval computation for depth 13, residue 3698. -/
theorem bounds_13_3698 : exactInterval 13 3698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3698 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3698) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3698 : oddCount 3698 13 = 7 ∧ acceleratedOrbit 13 3698 = 989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3698 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3698) = 3 ^ 7 * m + 989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3698.1, data_13_3698.2]

/-- Complete interval computation for depth 13, residue 3699. -/
theorem bounds_13_3699 : exactInterval 13 3699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3699 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3699) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3699 : oddCount 3699 13 = 7 ∧ acceleratedOrbit 13 3699 = 989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3699 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3699) = 3 ^ 7 * m + 989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3699.1, data_13_3699.2]

/-- Complete interval computation for depth 13, residue 3700. -/
theorem bounds_13_3700 : exactInterval 13 3700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3700 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3700) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3700 : oddCount 3700 13 = 7 ∧ acceleratedOrbit 13 3700 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3700 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3700) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3700.1, data_13_3700.2]

/-- Complete interval computation for depth 13, residue 3701. -/
theorem bounds_13_3701 : exactInterval 13 3701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3701 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3701) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3701 : oddCount 3701 13 = 7 ∧ acceleratedOrbit 13 3701 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3701 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3701) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3701.1, data_13_3701.2]

/-- Complete interval computation for depth 13, residue 3702. -/
theorem bounds_13_3702 : exactInterval 13 3702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3702 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3702) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3702 : oddCount 3702 13 = 5 ∧ acceleratedOrbit 13 3702 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3702 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3702) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3702.1, data_13_3702.2]

/-- Complete interval computation for depth 13, residue 3703. -/
theorem bounds_13_3703 : exactInterval 13 3703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3703 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3703) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3703 : oddCount 3703 13 = 5 ∧ acceleratedOrbit 13 3703 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3703 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3703) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3703.1, data_13_3703.2]

/-- Complete interval computation for depth 13, residue 3704. -/
theorem bounds_13_3704 : exactInterval 13 3704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3704 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3704) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3704 : oddCount 3704 13 = 7 ∧ acceleratedOrbit 13 3704 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3704 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3704) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3704.1, data_13_3704.2]

/-- Complete interval computation for depth 13, residue 3705. -/
theorem bounds_13_3705 : exactInterval 13 3705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3705 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3705) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3705 : oddCount 3705 13 = 9 ∧ acceleratedOrbit 13 3705 = 8909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3705 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3705) = 3 ^ 9 * m + 8909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3705.1, data_13_3705.2]

end Collatz.Research.StoppingAtlas.Batch0708
