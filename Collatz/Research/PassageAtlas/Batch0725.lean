import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0725

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23724. -/
theorem bounds_15_23724 : exactInterval 15 23724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23724 : oddCount 23724 15 = 5 ∧ acceleratedOrbit 15 23724 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23724) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23724.1, data_15_23724.2]

/-- Complete interval computation for depth 15, residue 23725. -/
theorem bounds_15_23725 : exactInterval 15 23725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23725 : oddCount 23725 15 = 5 ∧ acceleratedOrbit 15 23725 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23725) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23725.1, data_15_23725.2]

/-- Complete interval computation for depth 15, residue 23726. -/
theorem bounds_15_23726 : exactInterval 15 23726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23726 : oddCount 23726 15 = 5 ∧ acceleratedOrbit 15 23726 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23726) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23726.1, data_15_23726.2]

/-- Complete interval computation for depth 15, residue 23727. -/
theorem bounds_15_23727 : exactInterval 15 23727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23727 : oddCount 23727 15 = 10 ∧ acceleratedOrbit 15 23727 = 42761 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23727) = 3 ^ 10 * m + 42761 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23727.1, data_15_23727.2]

/-- Complete interval computation for depth 15, residue 23728. -/
theorem bounds_15_23728 : exactInterval 15 23728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23728 : oddCount 23728 15 = 6 ∧ acceleratedOrbit 15 23728 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23728) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23728.1, data_15_23728.2]

/-- Complete interval computation for depth 15, residue 23729. -/
theorem bounds_15_23729 : exactInterval 15 23729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23729 : oddCount 23729 15 = 8 ∧ acceleratedOrbit 15 23729 = 4754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23729) = 3 ^ 8 * m + 4754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23729.1, data_15_23729.2]

/-- Complete interval computation for depth 15, residue 23730. -/
theorem bounds_15_23730 : exactInterval 15 23730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23730 : oddCount 23730 15 = 8 ∧ acceleratedOrbit 15 23730 = 4754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23730) = 3 ^ 8 * m + 4754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23730.1, data_15_23730.2]

/-- Complete interval computation for depth 15, residue 23731. -/
theorem bounds_15_23731 : exactInterval 15 23731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23731 : oddCount 23731 15 = 8 ∧ acceleratedOrbit 15 23731 = 4754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23731) = 3 ^ 8 * m + 4754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23731.1, data_15_23731.2]

/-- Complete interval computation for depth 15, residue 23732. -/
theorem bounds_15_23732 : exactInterval 15 23732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23732 : oddCount 23732 15 = 6 ∧ acceleratedOrbit 15 23732 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23732) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23732.1, data_15_23732.2]

/-- Complete interval computation for depth 15, residue 23733. -/
theorem bounds_15_23733 : exactInterval 15 23733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23733 : oddCount 23733 15 = 6 ∧ acceleratedOrbit 15 23733 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23733) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23733.1, data_15_23733.2]

/-- Complete interval computation for depth 15, residue 23734. -/
theorem bounds_15_23734 : exactInterval 15 23734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23734 : oddCount 23734 15 = 8 ∧ acceleratedOrbit 15 23734 = 4753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23734) = 3 ^ 8 * m + 4753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23734.1, data_15_23734.2]

/-- Complete interval computation for depth 15, residue 23735. -/
theorem bounds_15_23735 : exactInterval 15 23735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23735 : oddCount 23735 15 = 8 ∧ acceleratedOrbit 15 23735 = 4753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23735) = 3 ^ 8 * m + 4753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23735.1, data_15_23735.2]

/-- Complete interval computation for depth 15, residue 23736. -/
theorem bounds_15_23736 : exactInterval 15 23736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23736 : oddCount 23736 15 = 6 ∧ acceleratedOrbit 15 23736 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23736) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23736.1, data_15_23736.2]

/-- Complete interval computation for depth 15, residue 23737. -/
theorem bounds_15_23737 : exactInterval 15 23737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23737 : oddCount 23737 15 = 8 ∧ acceleratedOrbit 15 23737 = 4754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23737) = 3 ^ 8 * m + 4754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23737.1, data_15_23737.2]

/-- Complete interval computation for depth 15, residue 23738. -/
theorem bounds_15_23738 : exactInterval 15 23738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23738 : oddCount 23738 15 = 6 ∧ acceleratedOrbit 15 23738 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23738) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23738.1, data_15_23738.2]

/-- Complete interval computation for depth 15, residue 23739. -/
theorem bounds_15_23739 : exactInterval 15 23739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23739 : oddCount 23739 15 = 9 ∧ acceleratedOrbit 15 23739 = 14261 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23739) = 3 ^ 9 * m + 14261 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23739.1, data_15_23739.2]

/-- Complete interval computation for depth 15, residue 23740. -/
theorem bounds_15_23740 : exactInterval 15 23740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23740 : oddCount 23740 15 = 7 ∧ acceleratedOrbit 15 23740 = 1585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23740) = 3 ^ 7 * m + 1585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23740.1, data_15_23740.2]

/-- Complete interval computation for depth 15, residue 23741. -/
theorem bounds_15_23741 : exactInterval 15 23741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23741 : oddCount 23741 15 = 7 ∧ acceleratedOrbit 15 23741 = 1585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23741) = 3 ^ 7 * m + 1585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23741.1, data_15_23741.2]

/-- Complete interval computation for depth 15, residue 23742. -/
theorem bounds_15_23742 : exactInterval 15 23742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23742 : oddCount 23742 15 = 7 ∧ acceleratedOrbit 15 23742 = 1585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23742) = 3 ^ 7 * m + 1585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23742.1, data_15_23742.2]

/-- Complete interval computation for depth 15, residue 23743. -/
theorem bounds_15_23743 : exactInterval 15 23743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23743 : oddCount 23743 15 = 10 ∧ acceleratedOrbit 15 23743 = 42788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23743) = 3 ^ 10 * m + 42788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23743.1, data_15_23743.2]

/-- Complete interval computation for depth 15, residue 23744. -/
theorem bounds_15_23744 : exactInterval 15 23744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23744 : oddCount 23744 15 = 4 ∧ acceleratedOrbit 15 23744 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23744) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23744.1, data_15_23744.2]

/-- Complete interval computation for depth 15, residue 23745. -/
theorem bounds_15_23745 : exactInterval 15 23745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23745 : oddCount 23745 15 = 7 ∧ acceleratedOrbit 15 23745 = 1586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23745) = 3 ^ 7 * m + 1586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23745.1, data_15_23745.2]

/-- Complete interval computation for depth 15, residue 23746. -/
theorem bounds_15_23746 : exactInterval 15 23746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23746 : oddCount 23746 15 = 7 ∧ acceleratedOrbit 15 23746 = 1586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23746) = 3 ^ 7 * m + 1586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23746.1, data_15_23746.2]

/-- Complete interval computation for depth 15, residue 23747. -/
theorem bounds_15_23747 : exactInterval 15 23747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23747 : oddCount 23747 15 = 7 ∧ acceleratedOrbit 15 23747 = 1586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23747) = 3 ^ 7 * m + 1586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23747.1, data_15_23747.2]

/-- Complete interval computation for depth 15, residue 23748. -/
theorem bounds_15_23748 : exactInterval 15 23748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23748 : oddCount 23748 15 = 6 ∧ acceleratedOrbit 15 23748 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23748) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23748.1, data_15_23748.2]

/-- Complete interval computation for depth 15, residue 23749. -/
theorem bounds_15_23749 : exactInterval 15 23749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23749 : oddCount 23749 15 = 6 ∧ acceleratedOrbit 15 23749 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23749) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23749.1, data_15_23749.2]

/-- Complete interval computation for depth 15, residue 23750. -/
theorem bounds_15_23750 : exactInterval 15 23750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23750 : oddCount 23750 15 = 6 ∧ acceleratedOrbit 15 23750 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23750) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23750.1, data_15_23750.2]

/-- Complete interval computation for depth 15, residue 23751. -/
theorem bounds_15_23751 : exactInterval 15 23751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23751 : oddCount 23751 15 = 9 ∧ acceleratedOrbit 15 23751 = 14269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23751) = 3 ^ 9 * m + 14269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23751.1, data_15_23751.2]

/-- Complete interval computation for depth 15, residue 23752. -/
theorem bounds_15_23752 : exactInterval 15 23752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23752 : oddCount 23752 15 = 6 ∧ acceleratedOrbit 15 23752 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23752) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23752.1, data_15_23752.2]

/-- Complete interval computation for depth 15, residue 23753. -/
theorem bounds_15_23753 : exactInterval 15 23753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23753 : oddCount 23753 15 = 7 ∧ acceleratedOrbit 15 23753 = 1586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23753) = 3 ^ 7 * m + 1586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23753.1, data_15_23753.2]

/-- Complete interval computation for depth 15, residue 23754. -/
theorem bounds_15_23754 : exactInterval 15 23754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23754 : oddCount 23754 15 = 6 ∧ acceleratedOrbit 15 23754 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23754) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23754.1, data_15_23754.2]

/-- Complete interval computation for depth 15, residue 23755. -/
theorem bounds_15_23755 : exactInterval 15 23755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23755 : oddCount 23755 15 = 7 ∧ acceleratedOrbit 15 23755 = 1586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23755) = 3 ^ 7 * m + 1586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23755.1, data_15_23755.2]

end Collatz.Research.PassageAtlas.Batch0725
