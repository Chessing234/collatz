import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0605

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19791. -/
theorem bounds_15_19791 : exactInterval 15 19791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19791 : oddCount 19791 15 = 7 ∧ acceleratedOrbit 15 19791 = 1321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19791) = 3 ^ 7 * m + 1321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19791.1, data_15_19791.2]

/-- Complete interval computation for depth 15, residue 19792. -/
theorem bounds_15_19792 : exactInterval 15 19792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19792 : oddCount 19792 15 = 3 ∧ acceleratedOrbit 15 19792 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19792) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19792.1, data_15_19792.2]

/-- Complete interval computation for depth 15, residue 19793. -/
theorem bounds_15_19793 : exactInterval 15 19793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19793 : oddCount 19793 15 = 11 ∧ acceleratedOrbit 15 19793 = 107027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19793) = 3 ^ 11 * m + 107027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19793.1, data_15_19793.2]

/-- Complete interval computation for depth 15, residue 19794. -/
theorem bounds_15_19794 : exactInterval 15 19794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19794 : oddCount 19794 15 = 11 ∧ acceleratedOrbit 15 19794 = 107027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19794) = 3 ^ 11 * m + 107027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19794.1, data_15_19794.2]

/-- Complete interval computation for depth 15, residue 19795. -/
theorem bounds_15_19795 : exactInterval 15 19795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19795 : oddCount 19795 15 = 11 ∧ acceleratedOrbit 15 19795 = 107027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19795) = 3 ^ 11 * m + 107027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19795.1, data_15_19795.2]

/-- Complete interval computation for depth 15, residue 19796. -/
theorem bounds_15_19796 : exactInterval 15 19796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19796 : oddCount 19796 15 = 3 ∧ acceleratedOrbit 15 19796 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19796) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19796.1, data_15_19796.2]

/-- Complete interval computation for depth 15, residue 19797. -/
theorem bounds_15_19797 : exactInterval 15 19797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19797 : oddCount 19797 15 = 3 ∧ acceleratedOrbit 15 19797 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19797) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19797.1, data_15_19797.2]

/-- Complete interval computation for depth 15, residue 19798. -/
theorem bounds_15_19798 : exactInterval 15 19798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19798 : oddCount 19798 15 = 9 ∧ acceleratedOrbit 15 19798 = 11897 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19798) = 3 ^ 9 * m + 11897 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19798.1, data_15_19798.2]

/-- Complete interval computation for depth 15, residue 19799. -/
theorem bounds_15_19799 : exactInterval 15 19799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19799 : oddCount 19799 15 = 9 ∧ acceleratedOrbit 15 19799 = 11897 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19799) = 3 ^ 9 * m + 11897 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19799.1, data_15_19799.2]

/-- Complete interval computation for depth 15, residue 19800. -/
theorem bounds_15_19800 : exactInterval 15 19800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19800 : oddCount 19800 15 = 9 ∧ acceleratedOrbit 15 19800 = 11906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19800) = 3 ^ 9 * m + 11906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19800.1, data_15_19800.2]

/-- Complete interval computation for depth 15, residue 19801. -/
theorem bounds_15_19801 : exactInterval 15 19801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19801 : oddCount 19801 15 = 8 ∧ acceleratedOrbit 15 19801 = 3968 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19801) = 3 ^ 8 * m + 3968 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19801.1, data_15_19801.2]

/-- Complete interval computation for depth 15, residue 19802. -/
theorem bounds_15_19802 : exactInterval 15 19802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19802 : oddCount 19802 15 = 9 ∧ acceleratedOrbit 15 19802 = 11906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19802) = 3 ^ 9 * m + 11906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19802.1, data_15_19802.2]

/-- Complete interval computation for depth 15, residue 19803. -/
theorem bounds_15_19803 : exactInterval 15 19803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19803 : oddCount 19803 15 = 9 ∧ acceleratedOrbit 15 19803 = 11897 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19803) = 3 ^ 9 * m + 11897 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19803.1, data_15_19803.2]

/-- Complete interval computation for depth 15, residue 19804. -/
theorem bounds_15_19804 : exactInterval 15 19804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19804 : oddCount 19804 15 = 9 ∧ acceleratedOrbit 15 19804 = 11906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19804) = 3 ^ 9 * m + 11906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19804.1, data_15_19804.2]

/-- Complete interval computation for depth 15, residue 19805. -/
theorem bounds_15_19805 : exactInterval 15 19805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19805 : oddCount 19805 15 = 9 ∧ acceleratedOrbit 15 19805 = 11906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19805) = 3 ^ 9 * m + 11906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19805.1, data_15_19805.2]

/-- Complete interval computation for depth 15, residue 19806. -/
theorem bounds_15_19806 : exactInterval 15 19806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19806 : oddCount 19806 15 = 9 ∧ acceleratedOrbit 15 19806 = 11900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19806) = 3 ^ 9 * m + 11900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19806.1, data_15_19806.2]

/-- Complete interval computation for depth 15, residue 19807. -/
theorem bounds_15_19807 : exactInterval 15 19807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19807 : oddCount 19807 15 = 9 ∧ acceleratedOrbit 15 19807 = 11900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19807) = 3 ^ 9 * m + 11900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19807.1, data_15_19807.2]

/-- Complete interval computation for depth 15, residue 19808. -/
theorem bounds_15_19808 : exactInterval 15 19808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19808 : oddCount 19808 15 = 6 ∧ acceleratedOrbit 15 19808 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19808) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19808.1, data_15_19808.2]

/-- Complete interval computation for depth 15, residue 19809. -/
theorem bounds_15_19809 : exactInterval 15 19809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19809 : oddCount 19809 15 = 8 ∧ acceleratedOrbit 15 19809 = 3968 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19809) = 3 ^ 8 * m + 3968 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19809.1, data_15_19809.2]

/-- Complete interval computation for depth 15, residue 19810. -/
theorem bounds_15_19810 : exactInterval 15 19810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19810 : oddCount 19810 15 = 4 ∧ acceleratedOrbit 15 19810 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19810) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19810.1, data_15_19810.2]

/-- Complete interval computation for depth 15, residue 19811. -/
theorem bounds_15_19811 : exactInterval 15 19811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19811 : oddCount 19811 15 = 4 ∧ acceleratedOrbit 15 19811 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19811) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19811.1, data_15_19811.2]

/-- Complete interval computation for depth 15, residue 19812. -/
theorem bounds_15_19812 : exactInterval 15 19812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19812 : oddCount 19812 15 = 4 ∧ acceleratedOrbit 15 19812 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19812) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19812.1, data_15_19812.2]

/-- Complete interval computation for depth 15, residue 19813. -/
theorem bounds_15_19813 : exactInterval 15 19813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19813 : oddCount 19813 15 = 4 ∧ acceleratedOrbit 15 19813 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19813) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19813.1, data_15_19813.2]

/-- Complete interval computation for depth 15, residue 19814. -/
theorem bounds_15_19814 : exactInterval 15 19814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19814 : oddCount 19814 15 = 4 ∧ acceleratedOrbit 15 19814 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19814) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19814.1, data_15_19814.2]

/-- Complete interval computation for depth 15, residue 19815. -/
theorem bounds_15_19815 : exactInterval 15 19815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19815 : oddCount 19815 15 = 11 ∧ acceleratedOrbit 15 19815 = 107129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19815) = 3 ^ 11 * m + 107129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19815.1, data_15_19815.2]

/-- Complete interval computation for depth 15, residue 19816. -/
theorem bounds_15_19816 : exactInterval 15 19816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19816 : oddCount 19816 15 = 6 ∧ acceleratedOrbit 15 19816 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19816) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19816.1, data_15_19816.2]

/-- Complete interval computation for depth 15, residue 19817. -/
theorem bounds_15_19817 : exactInterval 15 19817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19817 : oddCount 19817 15 = 10 ∧ acceleratedOrbit 15 19817 = 35720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19817) = 3 ^ 10 * m + 35720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19817.1, data_15_19817.2]

/-- Complete interval computation for depth 15, residue 19818. -/
theorem bounds_15_19818 : exactInterval 15 19818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19818 : oddCount 19818 15 = 6 ∧ acceleratedOrbit 15 19818 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19818) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19818.1, data_15_19818.2]

/-- Complete interval computation for depth 15, residue 19819. -/
theorem bounds_15_19819 : exactInterval 15 19819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19819 : oddCount 19819 15 = 11 ∧ acceleratedOrbit 15 19819 = 107162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19819) = 3 ^ 11 * m + 107162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19819.1, data_15_19819.2]

/-- Complete interval computation for depth 15, residue 19820. -/
theorem bounds_15_19820 : exactInterval 15 19820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19820 : oddCount 19820 15 = 8 ∧ acceleratedOrbit 15 19820 = 3970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19820) = 3 ^ 8 * m + 3970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19820.1, data_15_19820.2]

/-- Complete interval computation for depth 15, residue 19821. -/
theorem bounds_15_19821 : exactInterval 15 19821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19821 : oddCount 19821 15 = 8 ∧ acceleratedOrbit 15 19821 = 3970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19821) = 3 ^ 8 * m + 3970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19821.1, data_15_19821.2]

/-- Complete interval computation for depth 15, residue 19822. -/
theorem bounds_15_19822 : exactInterval 15 19822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19822 : oddCount 19822 15 = 8 ∧ acceleratedOrbit 15 19822 = 3970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19822) = 3 ^ 8 * m + 3970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19822.1, data_15_19822.2]

/-- Complete interval computation for depth 15, residue 19823. -/
theorem bounds_15_19823 : exactInterval 15 19823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19823 : oddCount 19823 15 = 9 ∧ acceleratedOrbit 15 19823 = 11909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19823) = 3 ^ 9 * m + 11909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19823.1, data_15_19823.2]

end Collatz.Research.PassageAtlas.Batch0605
