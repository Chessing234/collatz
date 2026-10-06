import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0788

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25788. -/
theorem bounds_15_25788 : exactInterval 15 25788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25788 : oddCount 25788 15 = 8 ∧ acceleratedOrbit 15 25788 = 5165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25788) = 3 ^ 8 * m + 5165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25788.1, data_15_25788.2]

/-- Complete interval computation for depth 15, residue 25789. -/
theorem bounds_15_25789 : exactInterval 15 25789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25789 : oddCount 25789 15 = 8 ∧ acceleratedOrbit 15 25789 = 5165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25789) = 3 ^ 8 * m + 5165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25789.1, data_15_25789.2]

/-- Complete interval computation for depth 15, residue 25790. -/
theorem bounds_15_25790 : exactInterval 15 25790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25790 : oddCount 25790 15 = 8 ∧ acceleratedOrbit 15 25790 = 5165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25790) = 3 ^ 8 * m + 5165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25790.1, data_15_25790.2]

/-- Complete interval computation for depth 15, residue 25791. -/
theorem bounds_15_25791 : exactInterval 15 25791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25791 : oddCount 25791 15 = 9 ∧ acceleratedOrbit 15 25791 = 15493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25791) = 3 ^ 9 * m + 15493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25791.1, data_15_25791.2]

/-- Complete interval computation for depth 15, residue 25792. -/
theorem bounds_15_25792 : exactInterval 15 25792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25792 : oddCount 25792 15 = 4 ∧ acceleratedOrbit 15 25792 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25792) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25792.1, data_15_25792.2]

/-- Complete interval computation for depth 15, residue 25793. -/
theorem bounds_15_25793 : exactInterval 15 25793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25793 : oddCount 25793 15 = 6 ∧ acceleratedOrbit 15 25793 = 574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25793) = 3 ^ 6 * m + 574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25793.1, data_15_25793.2]

/-- Complete interval computation for depth 15, residue 25794. -/
theorem bounds_15_25794 : exactInterval 15 25794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25794 : oddCount 25794 15 = 6 ∧ acceleratedOrbit 15 25794 = 574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25794) = 3 ^ 6 * m + 574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25794.1, data_15_25794.2]

/-- Complete interval computation for depth 15, residue 25795. -/
theorem bounds_15_25795 : exactInterval 15 25795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25795 : oddCount 25795 15 = 6 ∧ acceleratedOrbit 15 25795 = 574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25795) = 3 ^ 6 * m + 574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25795.1, data_15_25795.2]

/-- Complete interval computation for depth 15, residue 25796. -/
theorem bounds_15_25796 : exactInterval 15 25796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25796 : oddCount 25796 15 = 6 ∧ acceleratedOrbit 15 25796 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25796) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25796.1, data_15_25796.2]

/-- Complete interval computation for depth 15, residue 25797. -/
theorem bounds_15_25797 : exactInterval 15 25797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25797 : oddCount 25797 15 = 6 ∧ acceleratedOrbit 15 25797 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25797) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25797.1, data_15_25797.2]

/-- Complete interval computation for depth 15, residue 25798. -/
theorem bounds_15_25798 : exactInterval 15 25798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25798 : oddCount 25798 15 = 6 ∧ acceleratedOrbit 15 25798 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25798) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25798.1, data_15_25798.2]

/-- Complete interval computation for depth 15, residue 25799. -/
theorem bounds_15_25799 : exactInterval 15 25799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25799 : oddCount 25799 15 = 6 ∧ acceleratedOrbit 15 25799 = 574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25799) = 3 ^ 6 * m + 574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25799.1, data_15_25799.2]

/-- Complete interval computation for depth 15, residue 25800. -/
theorem bounds_15_25800 : exactInterval 15 25800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25800 : oddCount 25800 15 = 6 ∧ acceleratedOrbit 15 25800 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25800) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25800.1, data_15_25800.2]

/-- Complete interval computation for depth 15, residue 25801. -/
theorem bounds_15_25801 : exactInterval 15 25801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25801 : oddCount 25801 15 = 7 ∧ acceleratedOrbit 15 25801 = 1723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25801) = 3 ^ 7 * m + 1723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25801.1, data_15_25801.2]

/-- Complete interval computation for depth 15, residue 25802. -/
theorem bounds_15_25802 : exactInterval 15 25802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25802 : oddCount 25802 15 = 6 ∧ acceleratedOrbit 15 25802 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25802) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25802.1, data_15_25802.2]

/-- Complete interval computation for depth 15, residue 25803. -/
theorem bounds_15_25803 : exactInterval 15 25803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25803 : oddCount 25803 15 = 7 ∧ acceleratedOrbit 15 25803 = 1723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25803) = 3 ^ 7 * m + 1723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25803.1, data_15_25803.2]

/-- Complete interval computation for depth 15, residue 25804. -/
theorem bounds_15_25804 : exactInterval 15 25804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25804 : oddCount 25804 15 = 6 ∧ acceleratedOrbit 15 25804 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25804) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25804.1, data_15_25804.2]

/-- Complete interval computation for depth 15, residue 25805. -/
theorem bounds_15_25805 : exactInterval 15 25805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25805 : oddCount 25805 15 = 6 ∧ acceleratedOrbit 15 25805 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25805) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25805.1, data_15_25805.2]

/-- Complete interval computation for depth 15, residue 25806. -/
theorem bounds_15_25806 : exactInterval 15 25806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25806 : oddCount 25806 15 = 8 ∧ acceleratedOrbit 15 25806 = 5168 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25806) = 3 ^ 8 * m + 5168 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25806.1, data_15_25806.2]

/-- Complete interval computation for depth 15, residue 25807. -/
theorem bounds_15_25807 : exactInterval 15 25807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25807 : oddCount 25807 15 = 8 ∧ acceleratedOrbit 15 25807 = 5168 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25807) = 3 ^ 8 * m + 5168 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25807.1, data_15_25807.2]

/-- Complete interval computation for depth 15, residue 25808. -/
theorem bounds_15_25808 : exactInterval 15 25808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25808 : oddCount 25808 15 = 4 ∧ acceleratedOrbit 15 25808 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25808) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25808.1, data_15_25808.2]

/-- Complete interval computation for depth 15, residue 25809. -/
theorem bounds_15_25809 : exactInterval 15 25809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25809 : oddCount 25809 15 = 10 ∧ acceleratedOrbit 15 25809 = 46520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25809) = 3 ^ 10 * m + 46520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25809.1, data_15_25809.2]

/-- Complete interval computation for depth 15, residue 25810. -/
theorem bounds_15_25810 : exactInterval 15 25810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25810 : oddCount 25810 15 = 10 ∧ acceleratedOrbit 15 25810 = 46520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25810) = 3 ^ 10 * m + 46520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25810.1, data_15_25810.2]

/-- Complete interval computation for depth 15, residue 25811. -/
theorem bounds_15_25811 : exactInterval 15 25811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25811 : oddCount 25811 15 = 10 ∧ acceleratedOrbit 15 25811 = 46520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25811) = 3 ^ 10 * m + 46520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25811.1, data_15_25811.2]

/-- Complete interval computation for depth 15, residue 25812. -/
theorem bounds_15_25812 : exactInterval 15 25812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25812 : oddCount 25812 15 = 4 ∧ acceleratedOrbit 15 25812 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25812) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25812.1, data_15_25812.2]

/-- Complete interval computation for depth 15, residue 25813. -/
theorem bounds_15_25813 : exactInterval 15 25813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25813 : oddCount 25813 15 = 4 ∧ acceleratedOrbit 15 25813 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25813) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25813.1, data_15_25813.2]

/-- Complete interval computation for depth 15, residue 25814. -/
theorem bounds_15_25814 : exactInterval 15 25814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25814 : oddCount 25814 15 = 8 ∧ acceleratedOrbit 15 25814 = 5170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25814) = 3 ^ 8 * m + 5170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25814.1, data_15_25814.2]

/-- Complete interval computation for depth 15, residue 25815. -/
theorem bounds_15_25815 : exactInterval 15 25815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25815 : oddCount 25815 15 = 8 ∧ acceleratedOrbit 15 25815 = 5170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25815) = 3 ^ 8 * m + 5170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25815.1, data_15_25815.2]

/-- Complete interval computation for depth 15, residue 25816. -/
theorem bounds_15_25816 : exactInterval 15 25816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25816 : oddCount 25816 15 = 9 ∧ acceleratedOrbit 15 25816 = 15515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25816) = 3 ^ 9 * m + 15515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25816.1, data_15_25816.2]

/-- Complete interval computation for depth 15, residue 25817. -/
theorem bounds_15_25817 : exactInterval 15 25817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25817 : oddCount 25817 15 = 6 ∧ acceleratedOrbit 15 25817 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25817) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25817.1, data_15_25817.2]

/-- Complete interval computation for depth 15, residue 25818. -/
theorem bounds_15_25818 : exactInterval 15 25818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25818 : oddCount 25818 15 = 9 ∧ acceleratedOrbit 15 25818 = 15515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25818) = 3 ^ 9 * m + 15515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25818.1, data_15_25818.2]

/-- Complete interval computation for depth 15, residue 25819. -/
theorem bounds_15_25819 : exactInterval 15 25819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25819 : oddCount 25819 15 = 9 ∧ acceleratedOrbit 15 25819 = 15511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25819) = 3 ^ 9 * m + 15511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25819.1, data_15_25819.2]

/-- Complete interval computation for depth 15, residue 25820. -/
theorem bounds_15_25820 : exactInterval 15 25820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25820 : oddCount 25820 15 = 9 ∧ acceleratedOrbit 15 25820 = 15515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25820) = 3 ^ 9 * m + 15515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25820.1, data_15_25820.2]

end Collatz.Research.PassageAtlas.Batch0788
