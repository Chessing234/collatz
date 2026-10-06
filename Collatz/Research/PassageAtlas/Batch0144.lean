import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0144

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4685. -/
theorem bounds_15_4685 : exactInterval 15 4685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4685 : oddCount 4685 15 = 7 ∧ acceleratedOrbit 15 4685 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4685) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4685.1, data_15_4685.2]

/-- Complete interval computation for depth 15, residue 4686. -/
theorem bounds_15_4686 : exactInterval 15 4686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4686 : oddCount 4686 15 = 7 ∧ acceleratedOrbit 15 4686 = 313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4686) = 3 ^ 7 * m + 313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4686.1, data_15_4686.2]

/-- Complete interval computation for depth 15, residue 4687. -/
theorem bounds_15_4687 : exactInterval 15 4687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4687 : oddCount 4687 15 = 7 ∧ acceleratedOrbit 15 4687 = 313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4687) = 3 ^ 7 * m + 313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4687.1, data_15_4687.2]

/-- Complete interval computation for depth 15, residue 4688. -/
theorem bounds_15_4688 : exactInterval 15 4688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4688 : oddCount 4688 15 = 6 ∧ acceleratedOrbit 15 4688 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4688) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4688.1, data_15_4688.2]

/-- Complete interval computation for depth 15, residue 4689. -/
theorem bounds_15_4689 : exactInterval 15 4689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4689 : oddCount 4689 15 = 8 ∧ acceleratedOrbit 15 4689 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4689) = 3 ^ 8 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4689.1, data_15_4689.2]

/-- Complete interval computation for depth 15, residue 4690. -/
theorem bounds_15_4690 : exactInterval 15 4690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4690 : oddCount 4690 15 = 8 ∧ acceleratedOrbit 15 4690 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4690) = 3 ^ 8 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4690.1, data_15_4690.2]

/-- Complete interval computation for depth 15, residue 4691. -/
theorem bounds_15_4691 : exactInterval 15 4691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4691 : oddCount 4691 15 = 8 ∧ acceleratedOrbit 15 4691 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4691) = 3 ^ 8 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4691.1, data_15_4691.2]

/-- Complete interval computation for depth 15, residue 4692. -/
theorem bounds_15_4692 : exactInterval 15 4692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4692 : oddCount 4692 15 = 6 ∧ acceleratedOrbit 15 4692 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4692) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4692.1, data_15_4692.2]

/-- Complete interval computation for depth 15, residue 4693. -/
theorem bounds_15_4693 : exactInterval 15 4693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4693 : oddCount 4693 15 = 6 ∧ acceleratedOrbit 15 4693 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4693) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4693.1, data_15_4693.2]

/-- Complete interval computation for depth 15, residue 4694. -/
theorem bounds_15_4694 : exactInterval 15 4694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4694 : oddCount 4694 15 = 9 ∧ acceleratedOrbit 15 4694 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4694) = 3 ^ 9 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4694.1, data_15_4694.2]

/-- Complete interval computation for depth 15, residue 4695. -/
theorem bounds_15_4695 : exactInterval 15 4695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4695 : oddCount 4695 15 = 9 ∧ acceleratedOrbit 15 4695 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4695) = 3 ^ 9 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4695.1, data_15_4695.2]

/-- Complete interval computation for depth 15, residue 4696. -/
theorem bounds_15_4696 : exactInterval 15 4696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4696 : oddCount 4696 15 = 6 ∧ acceleratedOrbit 15 4696 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4696) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4696.1, data_15_4696.2]

/-- Complete interval computation for depth 15, residue 4697. -/
theorem bounds_15_4697 : exactInterval 15 4697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4697 : oddCount 4697 15 = 9 ∧ acceleratedOrbit 15 4697 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4697) = 3 ^ 9 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4697.1, data_15_4697.2]

/-- Complete interval computation for depth 15, residue 4698. -/
theorem bounds_15_4698 : exactInterval 15 4698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4698 : oddCount 4698 15 = 6 ∧ acceleratedOrbit 15 4698 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4698) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4698.1, data_15_4698.2]

/-- Complete interval computation for depth 15, residue 4699. -/
theorem bounds_15_4699 : exactInterval 15 4699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4699 : oddCount 4699 15 = 10 ∧ acceleratedOrbit 15 4699 = 8471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4699) = 3 ^ 10 * m + 8471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4699.1, data_15_4699.2]

/-- Complete interval computation for depth 15, residue 4700. -/
theorem bounds_15_4700 : exactInterval 15 4700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4700 : oddCount 4700 15 = 6 ∧ acceleratedOrbit 15 4700 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4700) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4700.1, data_15_4700.2]

/-- Complete interval computation for depth 15, residue 4701. -/
theorem bounds_15_4701 : exactInterval 15 4701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4701 : oddCount 4701 15 = 6 ∧ acceleratedOrbit 15 4701 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4701) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4701.1, data_15_4701.2]

/-- Complete interval computation for depth 15, residue 4702. -/
theorem bounds_15_4702 : exactInterval 15 4702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4702 : oddCount 4702 15 = 7 ∧ acceleratedOrbit 15 4702 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4702) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4702.1, data_15_4702.2]

/-- Complete interval computation for depth 15, residue 4703. -/
theorem bounds_15_4703 : exactInterval 15 4703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4703 : oddCount 4703 15 = 7 ∧ acceleratedOrbit 15 4703 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4703) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4703.1, data_15_4703.2]

/-- Complete interval computation for depth 15, residue 4704. -/
theorem bounds_15_4704 : exactInterval 15 4704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4704 : oddCount 4704 15 = 6 ∧ acceleratedOrbit 15 4704 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4704) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4704.1, data_15_4704.2]

/-- Complete interval computation for depth 15, residue 4705. -/
theorem bounds_15_4705 : exactInterval 15 4705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4705 : oddCount 4705 15 = 8 ∧ acceleratedOrbit 15 4705 = 944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4705) = 3 ^ 8 * m + 944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4705.1, data_15_4705.2]

/-- Complete interval computation for depth 15, residue 4706. -/
theorem bounds_15_4706 : exactInterval 15 4706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4706 : oddCount 4706 15 = 5 ∧ acceleratedOrbit 15 4706 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4706) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4706.1, data_15_4706.2]

/-- Complete interval computation for depth 15, residue 4707. -/
theorem bounds_15_4707 : exactInterval 15 4707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4707 : oddCount 4707 15 = 5 ∧ acceleratedOrbit 15 4707 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4707) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4707.1, data_15_4707.2]

/-- Complete interval computation for depth 15, residue 4708. -/
theorem bounds_15_4708 : exactInterval 15 4708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4708 : oddCount 4708 15 = 5 ∧ acceleratedOrbit 15 4708 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4708) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4708.1, data_15_4708.2]

/-- Complete interval computation for depth 15, residue 4709. -/
theorem bounds_15_4709 : exactInterval 15 4709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4709 : oddCount 4709 15 = 5 ∧ acceleratedOrbit 15 4709 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4709) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4709.1, data_15_4709.2]

/-- Complete interval computation for depth 15, residue 4710. -/
theorem bounds_15_4710 : exactInterval 15 4710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4710 : oddCount 4710 15 = 5 ∧ acceleratedOrbit 15 4710 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4710) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4710.1, data_15_4710.2]

/-- Complete interval computation for depth 15, residue 4711. -/
theorem bounds_15_4711 : exactInterval 15 4711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4711 : oddCount 4711 15 = 8 ∧ acceleratedOrbit 15 4711 = 944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4711) = 3 ^ 8 * m + 944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4711.1, data_15_4711.2]

/-- Complete interval computation for depth 15, residue 4712. -/
theorem bounds_15_4712 : exactInterval 15 4712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4712 : oddCount 4712 15 = 6 ∧ acceleratedOrbit 15 4712 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4712) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4712.1, data_15_4712.2]

/-- Complete interval computation for depth 15, residue 4713. -/
theorem bounds_15_4713 : exactInterval 15 4713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4713 : oddCount 4713 15 = 10 ∧ acceleratedOrbit 15 4713 = 8498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4713) = 3 ^ 10 * m + 8498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4713.1, data_15_4713.2]

/-- Complete interval computation for depth 15, residue 4714. -/
theorem bounds_15_4714 : exactInterval 15 4714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4714 : oddCount 4714 15 = 6 ∧ acceleratedOrbit 15 4714 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4714) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4714.1, data_15_4714.2]

/-- Complete interval computation for depth 15, residue 4715. -/
theorem bounds_15_4715 : exactInterval 15 4715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4715 : oddCount 4715 15 = 10 ∧ acceleratedOrbit 15 4715 = 8504 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4715) = 3 ^ 10 * m + 8504 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4715.1, data_15_4715.2]

/-- Complete interval computation for depth 15, residue 4716. -/
theorem bounds_15_4716 : exactInterval 15 4716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4716 : oddCount 4716 15 = 9 ∧ acceleratedOrbit 15 4716 = 2837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4716) = 3 ^ 9 * m + 2837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4716.1, data_15_4716.2]

/-- Complete interval computation for depth 15, residue 4717. -/
theorem bounds_15_4717 : exactInterval 15 4717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4717 : oddCount 4717 15 = 9 ∧ acceleratedOrbit 15 4717 = 2837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4717) = 3 ^ 9 * m + 2837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4717.1, data_15_4717.2]

end Collatz.Research.PassageAtlas.Batch0144
