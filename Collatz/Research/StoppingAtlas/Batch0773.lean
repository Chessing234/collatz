import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0773

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4689. -/
theorem bounds_13_4689 : exactInterval 13 4689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4689 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4689) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4689 : oddCount 4689 13 = 7 ∧ acceleratedOrbit 13 4689 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4689 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4689) = 3 ^ 7 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4689.1, data_13_4689.2]

/-- Complete interval computation for depth 13, residue 4690. -/
theorem bounds_13_4690 : exactInterval 13 4690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4690 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4690) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4690 : oddCount 4690 13 = 7 ∧ acceleratedOrbit 13 4690 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4690 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4690) = 3 ^ 7 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4690.1, data_13_4690.2]

/-- Complete interval computation for depth 13, residue 4691. -/
theorem bounds_13_4691 : exactInterval 13 4691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4691 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4691) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4691 : oddCount 4691 13 = 7 ∧ acceleratedOrbit 13 4691 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4691 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4691) = 3 ^ 7 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4691.1, data_13_4691.2]

/-- Complete interval computation for depth 13, residue 4692. -/
theorem bounds_13_4692 : exactInterval 13 4692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4692 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4692) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4692 : oddCount 4692 13 = 4 ∧ acceleratedOrbit 13 4692 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4692 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4692) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4692.1, data_13_4692.2]

/-- Complete interval computation for depth 13, residue 4693. -/
theorem bounds_13_4693 : exactInterval 13 4693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4693 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4693) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4693 : oddCount 4693 13 = 4 ∧ acceleratedOrbit 13 4693 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4693 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4693) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4693.1, data_13_4693.2]

/-- Complete interval computation for depth 13, residue 4694. -/
theorem bounds_13_4694 : exactInterval 13 4694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4694 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4694) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4694 : oddCount 4694 13 = 7 ∧ acceleratedOrbit 13 4694 = 1255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4694 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4694) = 3 ^ 7 * m + 1255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4694.1, data_13_4694.2]

/-- Complete interval computation for depth 13, residue 4695. -/
theorem bounds_13_4695 : exactInterval 13 4695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4695 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4695) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4695 : oddCount 4695 13 = 7 ∧ acceleratedOrbit 13 4695 = 1255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4695 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4695) = 3 ^ 7 * m + 1255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4695.1, data_13_4695.2]

/-- Complete interval computation for depth 13, residue 4696. -/
theorem bounds_13_4696 : exactInterval 13 4696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4696 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4696) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4696 : oddCount 4696 13 = 4 ∧ acceleratedOrbit 13 4696 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4696 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4696) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4696.1, data_13_4696.2]

/-- Complete interval computation for depth 13, residue 4697. -/
theorem bounds_13_4697 : exactInterval 13 4697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4697 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4697) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4697 : oddCount 4697 13 = 8 ∧ acceleratedOrbit 13 4697 = 3766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4697 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4697) = 3 ^ 8 * m + 3766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4697.1, data_13_4697.2]

/-- Complete interval computation for depth 13, residue 4698. -/
theorem bounds_13_4698 : exactInterval 13 4698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4698 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4698) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4698 : oddCount 4698 13 = 4 ∧ acceleratedOrbit 13 4698 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4698 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4698) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4698.1, data_13_4698.2]

/-- Complete interval computation for depth 13, residue 4699. -/
theorem bounds_13_4699 : exactInterval 13 4699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4699 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4699) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4699 : oddCount 4699 13 = 10 ∧ acceleratedOrbit 13 4699 = 33884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4699 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4699) = 3 ^ 10 * m + 33884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4699.1, data_13_4699.2]

/-- Complete interval computation for depth 13, residue 4700. -/
theorem bounds_13_4700 : exactInterval 13 4700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4700 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4700) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4700 : oddCount 4700 13 = 4 ∧ acceleratedOrbit 13 4700 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4700 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4700) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4700.1, data_13_4700.2]

/-- Complete interval computation for depth 13, residue 4701. -/
theorem bounds_13_4701 : exactInterval 13 4701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4701 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4701) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4701 : oddCount 4701 13 = 4 ∧ acceleratedOrbit 13 4701 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4701 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4701) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4701.1, data_13_4701.2]

/-- Complete interval computation for depth 13, residue 4702. -/
theorem bounds_13_4702 : exactInterval 13 4702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4702 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4702) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4702 : oddCount 4702 13 = 7 ∧ acceleratedOrbit 13 4702 = 1256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4702 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4702) = 3 ^ 7 * m + 1256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4702.1, data_13_4702.2]

/-- Complete interval computation for depth 13, residue 4703. -/
theorem bounds_13_4703 : exactInterval 13 4703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4703 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4703) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4703 : oddCount 4703 13 = 7 ∧ acceleratedOrbit 13 4703 = 1256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4703 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4703) = 3 ^ 7 * m + 1256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4703.1, data_13_4703.2]

/-- Complete interval computation for depth 13, residue 4704. -/
theorem bounds_13_4704 : exactInterval 13 4704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4704 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4704) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4704 : oddCount 4704 13 = 4 ∧ acceleratedOrbit 13 4704 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4704 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4704) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4704.1, data_13_4704.2]

end Collatz.Research.StoppingAtlas.Batch0773
