import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0480

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15695. -/
theorem bounds_15_15695 : exactInterval 15 15695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15695 : oddCount 15695 15 = 8 ∧ acceleratedOrbit 15 15695 = 3143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15695) = 3 ^ 8 * m + 3143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15695.1, data_15_15695.2]

/-- Complete interval computation for depth 15, residue 15696. -/
theorem bounds_15_15696 : exactInterval 15 15696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15696 : oddCount 15696 15 = 4 ∧ acceleratedOrbit 15 15696 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15696) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15696.1, data_15_15696.2]

/-- Complete interval computation for depth 15, residue 15697. -/
theorem bounds_15_15697 : exactInterval 15 15697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15697 : oddCount 15697 15 = 10 ∧ acceleratedOrbit 15 15697 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15697) = 3 ^ 10 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15697.1, data_15_15697.2]

/-- Complete interval computation for depth 15, residue 15698. -/
theorem bounds_15_15698 : exactInterval 15 15698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15698 : oddCount 15698 15 = 11 ∧ acceleratedOrbit 15 15698 = 84883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15698) = 3 ^ 11 * m + 84883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15698.1, data_15_15698.2]

/-- Complete interval computation for depth 15, residue 15699. -/
theorem bounds_15_15699 : exactInterval 15 15699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15699 : oddCount 15699 15 = 11 ∧ acceleratedOrbit 15 15699 = 84883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15699) = 3 ^ 11 * m + 84883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15699.1, data_15_15699.2]

/-- Complete interval computation for depth 15, residue 15700. -/
theorem bounds_15_15700 : exactInterval 15 15700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15700 : oddCount 15700 15 = 4 ∧ acceleratedOrbit 15 15700 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15700) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15700.1, data_15_15700.2]

/-- Complete interval computation for depth 15, residue 15701. -/
theorem bounds_15_15701 : exactInterval 15 15701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15701 : oddCount 15701 15 = 4 ∧ acceleratedOrbit 15 15701 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15701) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15701.1, data_15_15701.2]

/-- Complete interval computation for depth 15, residue 15702. -/
theorem bounds_15_15702 : exactInterval 15 15702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15702 : oddCount 15702 15 = 9 ∧ acceleratedOrbit 15 15702 = 9436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15702) = 3 ^ 9 * m + 9436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15702.1, data_15_15702.2]

/-- Complete interval computation for depth 15, residue 15703. -/
theorem bounds_15_15703 : exactInterval 15 15703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15703 : oddCount 15703 15 = 9 ∧ acceleratedOrbit 15 15703 = 9436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15703) = 3 ^ 9 * m + 9436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15703.1, data_15_15703.2]

/-- Complete interval computation for depth 15, residue 15704. -/
theorem bounds_15_15704 : exactInterval 15 15704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15704 : oddCount 15704 15 = 8 ∧ acceleratedOrbit 15 15704 = 3149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15704) = 3 ^ 8 * m + 3149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15704.1, data_15_15704.2]

/-- Complete interval computation for depth 15, residue 15705. -/
theorem bounds_15_15705 : exactInterval 15 15705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15705 : oddCount 15705 15 = 6 ∧ acceleratedOrbit 15 15705 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15705) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15705.1, data_15_15705.2]

/-- Complete interval computation for depth 15, residue 15706. -/
theorem bounds_15_15706 : exactInterval 15 15706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15706 : oddCount 15706 15 = 8 ∧ acceleratedOrbit 15 15706 = 3149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15706) = 3 ^ 8 * m + 3149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15706.1, data_15_15706.2]

/-- Complete interval computation for depth 15, residue 15707. -/
theorem bounds_15_15707 : exactInterval 15 15707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15707 : oddCount 15707 15 = 10 ∧ acceleratedOrbit 15 15707 = 28309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15707) = 3 ^ 10 * m + 28309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15707.1, data_15_15707.2]

/-- Complete interval computation for depth 15, residue 15708. -/
theorem bounds_15_15708 : exactInterval 15 15708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15708 : oddCount 15708 15 = 8 ∧ acceleratedOrbit 15 15708 = 3149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15708) = 3 ^ 8 * m + 3149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15708.1, data_15_15708.2]

/-- Complete interval computation for depth 15, residue 15709. -/
theorem bounds_15_15709 : exactInterval 15 15709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15709 : oddCount 15709 15 = 8 ∧ acceleratedOrbit 15 15709 = 3149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15709) = 3 ^ 8 * m + 3149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15709.1, data_15_15709.2]

/-- Complete interval computation for depth 15, residue 15710. -/
theorem bounds_15_15710 : exactInterval 15 15710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15710 : oddCount 15710 15 = 9 ∧ acceleratedOrbit 15 15710 = 9440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15710) = 3 ^ 9 * m + 9440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15710.1, data_15_15710.2]

/-- Complete interval computation for depth 15, residue 15711. -/
theorem bounds_15_15711 : exactInterval 15 15711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15711 : oddCount 15711 15 = 9 ∧ acceleratedOrbit 15 15711 = 9440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15711) = 3 ^ 9 * m + 9440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15711.1, data_15_15711.2]

/-- Complete interval computation for depth 15, residue 15712. -/
theorem bounds_15_15712 : exactInterval 15 15712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15712 : oddCount 15712 15 = 8 ∧ acceleratedOrbit 15 15712 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15712) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15712.1, data_15_15712.2]

/-- Complete interval computation for depth 15, residue 15713. -/
theorem bounds_15_15713 : exactInterval 15 15713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15713 : oddCount 15713 15 = 7 ∧ acceleratedOrbit 15 15713 = 1049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15713) = 3 ^ 7 * m + 1049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15713.1, data_15_15713.2]

/-- Complete interval computation for depth 15, residue 15714. -/
theorem bounds_15_15714 : exactInterval 15 15714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15714 : oddCount 15714 15 = 7 ∧ acceleratedOrbit 15 15714 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15714) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15714.1, data_15_15714.2]

/-- Complete interval computation for depth 15, residue 15715. -/
theorem bounds_15_15715 : exactInterval 15 15715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15715 : oddCount 15715 15 = 7 ∧ acceleratedOrbit 15 15715 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15715) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15715.1, data_15_15715.2]

/-- Complete interval computation for depth 15, residue 15716. -/
theorem bounds_15_15716 : exactInterval 15 15716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15716 : oddCount 15716 15 = 7 ∧ acceleratedOrbit 15 15716 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15716) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15716.1, data_15_15716.2]

/-- Complete interval computation for depth 15, residue 15717. -/
theorem bounds_15_15717 : exactInterval 15 15717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15717 : oddCount 15717 15 = 7 ∧ acceleratedOrbit 15 15717 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15717) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15717.1, data_15_15717.2]

/-- Complete interval computation for depth 15, residue 15718. -/
theorem bounds_15_15718 : exactInterval 15 15718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15718 : oddCount 15718 15 = 7 ∧ acceleratedOrbit 15 15718 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15718) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15718.1, data_15_15718.2]

/-- Complete interval computation for depth 15, residue 15719. -/
theorem bounds_15_15719 : exactInterval 15 15719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15719 : oddCount 15719 15 = 11 ∧ acceleratedOrbit 15 15719 = 84986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15719) = 3 ^ 11 * m + 84986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15719.1, data_15_15719.2]

/-- Complete interval computation for depth 15, residue 15720. -/
theorem bounds_15_15720 : exactInterval 15 15720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15720 : oddCount 15720 15 = 8 ∧ acceleratedOrbit 15 15720 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15720) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15720.1, data_15_15720.2]

/-- Complete interval computation for depth 15, residue 15721. -/
theorem bounds_15_15721 : exactInterval 15 15721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15721 : oddCount 15721 15 = 8 ∧ acceleratedOrbit 15 15721 = 3149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15721) = 3 ^ 8 * m + 3149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15721.1, data_15_15721.2]

/-- Complete interval computation for depth 15, residue 15722. -/
theorem bounds_15_15722 : exactInterval 15 15722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15722 : oddCount 15722 15 = 8 ∧ acceleratedOrbit 15 15722 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15722) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15722.1, data_15_15722.2]

/-- Complete interval computation for depth 15, residue 15723. -/
theorem bounds_15_15723 : exactInterval 15 15723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15723 : oddCount 15723 15 = 10 ∧ acceleratedOrbit 15 15723 = 28340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15723) = 3 ^ 10 * m + 28340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15723.1, data_15_15723.2]

/-- Complete interval computation for depth 15, residue 15724. -/
theorem bounds_15_15724 : exactInterval 15 15724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15724 : oddCount 15724 15 = 10 ∧ acceleratedOrbit 15 15724 = 28349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15724) = 3 ^ 10 * m + 28349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15724.1, data_15_15724.2]

/-- Complete interval computation for depth 15, residue 15725. -/
theorem bounds_15_15725 : exactInterval 15 15725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15725 : oddCount 15725 15 = 10 ∧ acceleratedOrbit 15 15725 = 28349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15725) = 3 ^ 10 * m + 28349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15725.1, data_15_15725.2]

/-- Complete interval computation for depth 15, residue 15726. -/
theorem bounds_15_15726 : exactInterval 15 15726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15726 : oddCount 15726 15 = 10 ∧ acceleratedOrbit 15 15726 = 28349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15726) = 3 ^ 10 * m + 28349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15726.1, data_15_15726.2]

/-- Complete interval computation for depth 15, residue 15727. -/
theorem bounds_15_15727 : exactInterval 15 15727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15727 : oddCount 15727 15 = 9 ∧ acceleratedOrbit 15 15727 = 9449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15727) = 3 ^ 9 * m + 9449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15727.1, data_15_15727.2]

end Collatz.Research.PassageAtlas.Batch0480
