import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0727

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23789. -/
theorem bounds_15_23789 : exactInterval 15 23789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23789 : oddCount 23789 15 = 6 ∧ acceleratedOrbit 15 23789 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23789) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23789.1, data_15_23789.2]

/-- Complete interval computation for depth 15, residue 23790. -/
theorem bounds_15_23790 : exactInterval 15 23790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23790 : oddCount 23790 15 = 6 ∧ acceleratedOrbit 15 23790 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23790) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23790.1, data_15_23790.2]

/-- Complete interval computation for depth 15, residue 23791. -/
theorem bounds_15_23791 : exactInterval 15 23791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23791 : oddCount 23791 15 = 11 ∧ acceleratedOrbit 15 23791 = 128623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23791) = 3 ^ 11 * m + 128623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23791.1, data_15_23791.2]

/-- Complete interval computation for depth 15, residue 23792. -/
theorem bounds_15_23792 : exactInterval 15 23792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23792 : oddCount 23792 15 = 8 ∧ acceleratedOrbit 15 23792 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23792) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23792.1, data_15_23792.2]

/-- Complete interval computation for depth 15, residue 23793. -/
theorem bounds_15_23793 : exactInterval 15 23793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23793 : oddCount 23793 15 = 8 ∧ acceleratedOrbit 15 23793 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23793) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23793.1, data_15_23793.2]

/-- Complete interval computation for depth 15, residue 23794. -/
theorem bounds_15_23794 : exactInterval 15 23794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23794 : oddCount 23794 15 = 9 ∧ acceleratedOrbit 15 23794 = 14296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23794) = 3 ^ 9 * m + 14296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23794.1, data_15_23794.2]

/-- Complete interval computation for depth 15, residue 23795. -/
theorem bounds_15_23795 : exactInterval 15 23795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23795 : oddCount 23795 15 = 9 ∧ acceleratedOrbit 15 23795 = 14296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23795) = 3 ^ 9 * m + 14296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23795.1, data_15_23795.2]

/-- Complete interval computation for depth 15, residue 23796. -/
theorem bounds_15_23796 : exactInterval 15 23796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23796 : oddCount 23796 15 = 8 ∧ acceleratedOrbit 15 23796 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23796) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23796.1, data_15_23796.2]

/-- Complete interval computation for depth 15, residue 23797. -/
theorem bounds_15_23797 : exactInterval 15 23797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23797 : oddCount 23797 15 = 8 ∧ acceleratedOrbit 15 23797 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23797) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23797.1, data_15_23797.2]

/-- Complete interval computation for depth 15, residue 23798. -/
theorem bounds_15_23798 : exactInterval 15 23798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23798 : oddCount 23798 15 = 6 ∧ acceleratedOrbit 15 23798 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23798) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23798.1, data_15_23798.2]

/-- Complete interval computation for depth 15, residue 23799. -/
theorem bounds_15_23799 : exactInterval 15 23799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23799 : oddCount 23799 15 = 6 ∧ acceleratedOrbit 15 23799 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23799) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23799.1, data_15_23799.2]

/-- Complete interval computation for depth 15, residue 23800. -/
theorem bounds_15_23800 : exactInterval 15 23800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23800 : oddCount 23800 15 = 7 ∧ acceleratedOrbit 15 23800 = 1589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23800) = 3 ^ 7 * m + 1589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23800.1, data_15_23800.2]

/-- Complete interval computation for depth 15, residue 23801. -/
theorem bounds_15_23801 : exactInterval 15 23801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23801 : oddCount 23801 15 = 9 ∧ acceleratedOrbit 15 23801 = 14300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23801) = 3 ^ 9 * m + 14300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23801.1, data_15_23801.2]

/-- Complete interval computation for depth 15, residue 23802. -/
theorem bounds_15_23802 : exactInterval 15 23802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23802 : oddCount 23802 15 = 7 ∧ acceleratedOrbit 15 23802 = 1589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23802) = 3 ^ 7 * m + 1589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23802.1, data_15_23802.2]

/-- Complete interval computation for depth 15, residue 23803. -/
theorem bounds_15_23803 : exactInterval 15 23803 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23803) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23803 : oddCount 23803 15 = 9 ∧ acceleratedOrbit 15 23803 = 14299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23803) = 3 ^ 9 * m + 14299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23803.1, data_15_23803.2]

/-- Complete interval computation for depth 15, residue 23804. -/
theorem bounds_15_23804 : exactInterval 15 23804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23804 : oddCount 23804 15 = 7 ∧ acceleratedOrbit 15 23804 = 1589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23804) = 3 ^ 7 * m + 1589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23804.1, data_15_23804.2]

/-- Complete interval computation for depth 15, residue 23805. -/
theorem bounds_15_23805 : exactInterval 15 23805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23805 : oddCount 23805 15 = 7 ∧ acceleratedOrbit 15 23805 = 1589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23805) = 3 ^ 7 * m + 1589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23805.1, data_15_23805.2]

/-- Complete interval computation for depth 15, residue 23806. -/
theorem bounds_15_23806 : exactInterval 15 23806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23806 : oddCount 23806 15 = 13 ∧ acceleratedOrbit 15 23806 = 1158380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23806) = 3 ^ 13 * m + 1158380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23806.1, data_15_23806.2]

/-- Complete interval computation for depth 15, residue 23807. -/
theorem bounds_15_23807 : exactInterval 15 23807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23807 : oddCount 23807 15 = 13 ∧ acceleratedOrbit 15 23807 = 1158380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23807) = 3 ^ 13 * m + 1158380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23807.1, data_15_23807.2]

/-- Complete interval computation for depth 15, residue 23808. -/
theorem bounds_15_23808 : exactInterval 15 23808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23808 : oddCount 23808 15 = 3 ∧ acceleratedOrbit 15 23808 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23808) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23808.1, data_15_23808.2]

/-- Complete interval computation for depth 15, residue 23809. -/
theorem bounds_15_23809 : exactInterval 15 23809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23809 : oddCount 23809 15 = 8 ∧ acceleratedOrbit 15 23809 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23809) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23809.1, data_15_23809.2]

/-- Complete interval computation for depth 15, residue 23810. -/
theorem bounds_15_23810 : exactInterval 15 23810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23810 : oddCount 23810 15 = 10 ∧ acceleratedOrbit 15 23810 = 42920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23810) = 3 ^ 10 * m + 42920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23810.1, data_15_23810.2]

/-- Complete interval computation for depth 15, residue 23811. -/
theorem bounds_15_23811 : exactInterval 15 23811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23811 : oddCount 23811 15 = 10 ∧ acceleratedOrbit 15 23811 = 42920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23811) = 3 ^ 10 * m + 42920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23811.1, data_15_23811.2]

/-- Complete interval computation for depth 15, residue 23812. -/
theorem bounds_15_23812 : exactInterval 15 23812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23812 : oddCount 23812 15 = 4 ∧ acceleratedOrbit 15 23812 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23812) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23812.1, data_15_23812.2]

/-- Complete interval computation for depth 15, residue 23813. -/
theorem bounds_15_23813 : exactInterval 15 23813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23813 : oddCount 23813 15 = 4 ∧ acceleratedOrbit 15 23813 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23813) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23813.1, data_15_23813.2]

/-- Complete interval computation for depth 15, residue 23814. -/
theorem bounds_15_23814 : exactInterval 15 23814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23814 : oddCount 23814 15 = 4 ∧ acceleratedOrbit 15 23814 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23814) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23814.1, data_15_23814.2]

/-- Complete interval computation for depth 15, residue 23815. -/
theorem bounds_15_23815 : exactInterval 15 23815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23815 : oddCount 23815 15 = 10 ∧ acceleratedOrbit 15 23815 = 42920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23815) = 3 ^ 10 * m + 42920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23815.1, data_15_23815.2]

/-- Complete interval computation for depth 15, residue 23816. -/
theorem bounds_15_23816 : exactInterval 15 23816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23816 : oddCount 23816 15 = 7 ∧ acceleratedOrbit 15 23816 = 1592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23816) = 3 ^ 7 * m + 1592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23816.1, data_15_23816.2]

/-- Complete interval computation for depth 15, residue 23817. -/
theorem bounds_15_23817 : exactInterval 15 23817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23817 : oddCount 23817 15 = 9 ∧ acceleratedOrbit 15 23817 = 14309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23817) = 3 ^ 9 * m + 14309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23817.1, data_15_23817.2]

/-- Complete interval computation for depth 15, residue 23818. -/
theorem bounds_15_23818 : exactInterval 15 23818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23818 : oddCount 23818 15 = 7 ∧ acceleratedOrbit 15 23818 = 1592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23818) = 3 ^ 7 * m + 1592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23818.1, data_15_23818.2]

/-- Complete interval computation for depth 15, residue 23819. -/
theorem bounds_15_23819 : exactInterval 15 23819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23819 : oddCount 23819 15 = 6 ∧ acceleratedOrbit 15 23819 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23819) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23819.1, data_15_23819.2]

/-- Complete interval computation for depth 15, residue 23820. -/
theorem bounds_15_23820 : exactInterval 15 23820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23820 : oddCount 23820 15 = 7 ∧ acceleratedOrbit 15 23820 = 1592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23820) = 3 ^ 7 * m + 1592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23820.1, data_15_23820.2]

/-- Complete interval computation for depth 15, residue 23821. -/
theorem bounds_15_23821 : exactInterval 15 23821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23821 : oddCount 23821 15 = 7 ∧ acceleratedOrbit 15 23821 = 1592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23821) = 3 ^ 7 * m + 1592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23821.1, data_15_23821.2]

end Collatz.Research.PassageAtlas.Batch0727
