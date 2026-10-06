import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0147

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4784. -/
theorem bounds_15_4784 : exactInterval 15 4784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4784 : oddCount 4784 15 = 7 ∧ acceleratedOrbit 15 4784 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4784) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4784.1, data_15_4784.2]

/-- Complete interval computation for depth 15, residue 4785. -/
theorem bounds_15_4785 : exactInterval 15 4785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4785 : oddCount 4785 15 = 8 ∧ acceleratedOrbit 15 4785 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4785) = 3 ^ 8 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4785.1, data_15_4785.2]

/-- Complete interval computation for depth 15, residue 4786. -/
theorem bounds_15_4786 : exactInterval 15 4786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4786 : oddCount 4786 15 = 8 ∧ acceleratedOrbit 15 4786 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4786) = 3 ^ 8 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4786.1, data_15_4786.2]

/-- Complete interval computation for depth 15, residue 4787. -/
theorem bounds_15_4787 : exactInterval 15 4787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4787 : oddCount 4787 15 = 8 ∧ acceleratedOrbit 15 4787 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4787) = 3 ^ 8 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4787.1, data_15_4787.2]

/-- Complete interval computation for depth 15, residue 4788. -/
theorem bounds_15_4788 : exactInterval 15 4788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4788 : oddCount 4788 15 = 7 ∧ acceleratedOrbit 15 4788 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4788) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4788.1, data_15_4788.2]

/-- Complete interval computation for depth 15, residue 4789. -/
theorem bounds_15_4789 : exactInterval 15 4789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4789 : oddCount 4789 15 = 7 ∧ acceleratedOrbit 15 4789 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4789) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4789.1, data_15_4789.2]

/-- Complete interval computation for depth 15, residue 4790. -/
theorem bounds_15_4790 : exactInterval 15 4790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4790 : oddCount 4790 15 = 7 ∧ acceleratedOrbit 15 4790 = 320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4790) = 3 ^ 7 * m + 320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4790.1, data_15_4790.2]

/-- Complete interval computation for depth 15, residue 4791. -/
theorem bounds_15_4791 : exactInterval 15 4791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4791 : oddCount 4791 15 = 7 ∧ acceleratedOrbit 15 4791 = 320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4791) = 3 ^ 7 * m + 320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4791.1, data_15_4791.2]

/-- Complete interval computation for depth 15, residue 4792. -/
theorem bounds_15_4792 : exactInterval 15 4792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4792 : oddCount 4792 15 = 7 ∧ acceleratedOrbit 15 4792 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4792) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4792.1, data_15_4792.2]

/-- Complete interval computation for depth 15, residue 4793. -/
theorem bounds_15_4793 : exactInterval 15 4793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4793 : oddCount 4793 15 = 8 ∧ acceleratedOrbit 15 4793 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4793) = 3 ^ 8 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4793.1, data_15_4793.2]

/-- Complete interval computation for depth 15, residue 4794. -/
theorem bounds_15_4794 : exactInterval 15 4794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4794 : oddCount 4794 15 = 7 ∧ acceleratedOrbit 15 4794 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4794) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4794.1, data_15_4794.2]

/-- Complete interval computation for depth 15, residue 4795. -/
theorem bounds_15_4795 : exactInterval 15 4795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4795 : oddCount 4795 15 = 9 ∧ acceleratedOrbit 15 4795 = 2882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4795) = 3 ^ 9 * m + 2882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4795.1, data_15_4795.2]

/-- Complete interval computation for depth 15, residue 4796. -/
theorem bounds_15_4796 : exactInterval 15 4796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4796 : oddCount 4796 15 = 8 ∧ acceleratedOrbit 15 4796 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4796) = 3 ^ 8 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4796.1, data_15_4796.2]

/-- Complete interval computation for depth 15, residue 4797. -/
theorem bounds_15_4797 : exactInterval 15 4797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4797 : oddCount 4797 15 = 8 ∧ acceleratedOrbit 15 4797 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4797) = 3 ^ 8 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4797.1, data_15_4797.2]

/-- Complete interval computation for depth 15, residue 4798. -/
theorem bounds_15_4798 : exactInterval 15 4798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4798 : oddCount 4798 15 = 8 ∧ acceleratedOrbit 15 4798 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4798) = 3 ^ 8 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4798.1, data_15_4798.2]

/-- Complete interval computation for depth 15, residue 4799. -/
theorem bounds_15_4799 : exactInterval 15 4799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4799 : oddCount 4799 15 = 10 ∧ acceleratedOrbit 15 4799 = 8650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4799) = 3 ^ 10 * m + 8650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4799.1, data_15_4799.2]

/-- Complete interval computation for depth 15, residue 4800. -/
theorem bounds_15_4800 : exactInterval 15 4800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4800 : oddCount 4800 15 = 3 ∧ acceleratedOrbit 15 4800 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4800) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4800.1, data_15_4800.2]

/-- Complete interval computation for depth 15, residue 4801. -/
theorem bounds_15_4801 : exactInterval 15 4801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4801 : oddCount 4801 15 = 7 ∧ acceleratedOrbit 15 4801 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4801) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4801.1, data_15_4801.2]

/-- Complete interval computation for depth 15, residue 4802. -/
theorem bounds_15_4802 : exactInterval 15 4802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4802 : oddCount 4802 15 = 10 ∧ acceleratedOrbit 15 4802 = 8666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4802) = 3 ^ 10 * m + 8666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4802.1, data_15_4802.2]

/-- Complete interval computation for depth 15, residue 4803. -/
theorem bounds_15_4803 : exactInterval 15 4803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4803 : oddCount 4803 15 = 10 ∧ acceleratedOrbit 15 4803 = 8666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4803) = 3 ^ 10 * m + 8666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4803.1, data_15_4803.2]

/-- Complete interval computation for depth 15, residue 4804. -/
theorem bounds_15_4804 : exactInterval 15 4804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4804 : oddCount 4804 15 = 8 ∧ acceleratedOrbit 15 4804 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4804) = 3 ^ 8 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4804.1, data_15_4804.2]

/-- Complete interval computation for depth 15, residue 4805. -/
theorem bounds_15_4805 : exactInterval 15 4805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4805 : oddCount 4805 15 = 8 ∧ acceleratedOrbit 15 4805 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4805) = 3 ^ 8 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4805.1, data_15_4805.2]

/-- Complete interval computation for depth 15, residue 4806. -/
theorem bounds_15_4806 : exactInterval 15 4806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4806 : oddCount 4806 15 = 8 ∧ acceleratedOrbit 15 4806 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4806) = 3 ^ 8 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4806.1, data_15_4806.2]

/-- Complete interval computation for depth 15, residue 4807. -/
theorem bounds_15_4807 : exactInterval 15 4807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4807 : oddCount 4807 15 = 6 ∧ acceleratedOrbit 15 4807 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4807) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4807.1, data_15_4807.2]

/-- Complete interval computation for depth 15, residue 4808. -/
theorem bounds_15_4808 : exactInterval 15 4808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4808 : oddCount 4808 15 = 8 ∧ acceleratedOrbit 15 4808 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4808) = 3 ^ 8 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4808.1, data_15_4808.2]

/-- Complete interval computation for depth 15, residue 4809. -/
theorem bounds_15_4809 : exactInterval 15 4809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4809 : oddCount 4809 15 = 8 ∧ acceleratedOrbit 15 4809 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4809) = 3 ^ 8 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4809.1, data_15_4809.2]

/-- Complete interval computation for depth 15, residue 4810. -/
theorem bounds_15_4810 : exactInterval 15 4810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4810 : oddCount 4810 15 = 8 ∧ acceleratedOrbit 15 4810 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4810) = 3 ^ 8 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4810.1, data_15_4810.2]

/-- Complete interval computation for depth 15, residue 4811. -/
theorem bounds_15_4811 : exactInterval 15 4811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4811 : oddCount 4811 15 = 8 ∧ acceleratedOrbit 15 4811 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4811) = 3 ^ 8 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4811.1, data_15_4811.2]

/-- Complete interval computation for depth 15, residue 4812. -/
theorem bounds_15_4812 : exactInterval 15 4812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4812 : oddCount 4812 15 = 8 ∧ acceleratedOrbit 15 4812 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4812) = 3 ^ 8 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4812.1, data_15_4812.2]

/-- Complete interval computation for depth 15, residue 4813. -/
theorem bounds_15_4813 : exactInterval 15 4813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4813 : oddCount 4813 15 = 8 ∧ acceleratedOrbit 15 4813 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4813) = 3 ^ 8 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4813.1, data_15_4813.2]

/-- Complete interval computation for depth 15, residue 4814. -/
theorem bounds_15_4814 : exactInterval 15 4814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4814 : oddCount 4814 15 = 10 ∧ acceleratedOrbit 15 4814 = 8680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4814) = 3 ^ 10 * m + 8680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4814.1, data_15_4814.2]

/-- Complete interval computation for depth 15, residue 4815. -/
theorem bounds_15_4815 : exactInterval 15 4815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4815 : oddCount 4815 15 = 10 ∧ acceleratedOrbit 15 4815 = 8680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4815) = 3 ^ 10 * m + 8680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4815.1, data_15_4815.2]

end Collatz.Research.PassageAtlas.Batch0147
