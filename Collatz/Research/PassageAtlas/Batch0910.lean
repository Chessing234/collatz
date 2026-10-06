import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0910

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29786. -/
theorem bounds_15_29786 : exactInterval 15 29786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29786 : oddCount 29786 15 = 5 ∧ acceleratedOrbit 15 29786 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29786) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29786.1, data_15_29786.2]

/-- Complete interval computation for depth 15, residue 29787. -/
theorem bounds_15_29787 : exactInterval 15 29787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29787 : oddCount 29787 15 = 11 ∧ acceleratedOrbit 15 29787 = 161041 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29787) = 3 ^ 11 * m + 161041 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29787.1, data_15_29787.2]

/-- Complete interval computation for depth 15, residue 29788. -/
theorem bounds_15_29788 : exactInterval 15 29788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29788 : oddCount 29788 15 = 5 ∧ acceleratedOrbit 15 29788 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29788) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29788.1, data_15_29788.2]

/-- Complete interval computation for depth 15, residue 29789. -/
theorem bounds_15_29789 : exactInterval 15 29789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29789 : oddCount 29789 15 = 5 ∧ acceleratedOrbit 15 29789 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29789) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29789.1, data_15_29789.2]

/-- Complete interval computation for depth 15, residue 29790. -/
theorem bounds_15_29790 : exactInterval 15 29790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29790 : oddCount 29790 15 = 9 ∧ acceleratedOrbit 15 29790 = 17896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29790) = 3 ^ 9 * m + 17896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29790.1, data_15_29790.2]

/-- Complete interval computation for depth 15, residue 29791. -/
theorem bounds_15_29791 : exactInterval 15 29791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29791 : oddCount 29791 15 = 9 ∧ acceleratedOrbit 15 29791 = 17896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29791) = 3 ^ 9 * m + 17896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29791.1, data_15_29791.2]

/-- Complete interval computation for depth 15, residue 29792. -/
theorem bounds_15_29792 : exactInterval 15 29792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29792 : oddCount 29792 15 = 4 ∧ acceleratedOrbit 15 29792 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29792) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29792.1, data_15_29792.2]

/-- Complete interval computation for depth 15, residue 29793. -/
theorem bounds_15_29793 : exactInterval 15 29793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29793 : oddCount 29793 15 = 9 ∧ acceleratedOrbit 15 29793 = 17900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29793) = 3 ^ 9 * m + 17900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29793.1, data_15_29793.2]

/-- Complete interval computation for depth 15, residue 29794. -/
theorem bounds_15_29794 : exactInterval 15 29794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29794 : oddCount 29794 15 = 8 ∧ acceleratedOrbit 15 29794 = 5969 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29794) = 3 ^ 8 * m + 5969 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29794.1, data_15_29794.2]

/-- Complete interval computation for depth 15, residue 29795. -/
theorem bounds_15_29795 : exactInterval 15 29795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29795 : oddCount 29795 15 = 8 ∧ acceleratedOrbit 15 29795 = 5969 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29795) = 3 ^ 8 * m + 5969 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29795.1, data_15_29795.2]

/-- Complete interval computation for depth 15, residue 29796. -/
theorem bounds_15_29796 : exactInterval 15 29796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29796 : oddCount 29796 15 = 8 ∧ acceleratedOrbit 15 29796 = 5969 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29796) = 3 ^ 8 * m + 5969 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29796.1, data_15_29796.2]

/-- Complete interval computation for depth 15, residue 29797. -/
theorem bounds_15_29797 : exactInterval 15 29797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29797 : oddCount 29797 15 = 8 ∧ acceleratedOrbit 15 29797 = 5969 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29797) = 3 ^ 8 * m + 5969 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29797.1, data_15_29797.2]

/-- Complete interval computation for depth 15, residue 29798. -/
theorem bounds_15_29798 : exactInterval 15 29798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29798 : oddCount 29798 15 = 8 ∧ acceleratedOrbit 15 29798 = 5969 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29798) = 3 ^ 8 * m + 5969 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29798.1, data_15_29798.2]

/-- Complete interval computation for depth 15, residue 29799. -/
theorem bounds_15_29799 : exactInterval 15 29799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29799 : oddCount 29799 15 = 11 ∧ acceleratedOrbit 15 29799 = 161104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29799) = 3 ^ 11 * m + 161104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29799.1, data_15_29799.2]

/-- Complete interval computation for depth 15, residue 29800. -/
theorem bounds_15_29800 : exactInterval 15 29800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29800 : oddCount 29800 15 = 4 ∧ acceleratedOrbit 15 29800 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29800) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29800.1, data_15_29800.2]

/-- Complete interval computation for depth 15, residue 29801. -/
theorem bounds_15_29801 : exactInterval 15 29801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29801 : oddCount 29801 15 = 9 ∧ acceleratedOrbit 15 29801 = 17903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29801) = 3 ^ 9 * m + 17903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29801.1, data_15_29801.2]

/-- Complete interval computation for depth 15, residue 29802. -/
theorem bounds_15_29802 : exactInterval 15 29802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29802 : oddCount 29802 15 = 4 ∧ acceleratedOrbit 15 29802 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29802) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29802.1, data_15_29802.2]

/-- Complete interval computation for depth 15, residue 29803. -/
theorem bounds_15_29803 : exactInterval 15 29803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29803 : oddCount 29803 15 = 8 ∧ acceleratedOrbit 15 29803 = 5968 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29803) = 3 ^ 8 * m + 5968 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29803.1, data_15_29803.2]

/-- Complete interval computation for depth 15, residue 29804. -/
theorem bounds_15_29804 : exactInterval 15 29804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29804 : oddCount 29804 15 = 9 ∧ acceleratedOrbit 15 29804 = 17906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29804) = 3 ^ 9 * m + 17906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29804.1, data_15_29804.2]

/-- Complete interval computation for depth 15, residue 29805. -/
theorem bounds_15_29805 : exactInterval 15 29805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29805 : oddCount 29805 15 = 9 ∧ acceleratedOrbit 15 29805 = 17906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29805) = 3 ^ 9 * m + 17906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29805.1, data_15_29805.2]

/-- Complete interval computation for depth 15, residue 29806. -/
theorem bounds_15_29806 : exactInterval 15 29806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29806 : oddCount 29806 15 = 9 ∧ acceleratedOrbit 15 29806 = 17906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29806) = 3 ^ 9 * m + 17906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29806.1, data_15_29806.2]

/-- Complete interval computation for depth 15, residue 29807. -/
theorem bounds_15_29807 : exactInterval 15 29807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29807 : oddCount 29807 15 = 10 ∧ acceleratedOrbit 15 29807 = 53716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29807) = 3 ^ 10 * m + 53716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29807.1, data_15_29807.2]

/-- Complete interval computation for depth 15, residue 29808. -/
theorem bounds_15_29808 : exactInterval 15 29808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29808 : oddCount 29808 15 = 7 ∧ acceleratedOrbit 15 29808 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29808) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29808.1, data_15_29808.2]

/-- Complete interval computation for depth 15, residue 29809. -/
theorem bounds_15_29809 : exactInterval 15 29809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29809 : oddCount 29809 15 = 4 ∧ acceleratedOrbit 15 29809 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29809) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29809.1, data_15_29809.2]

/-- Complete interval computation for depth 15, residue 29810. -/
theorem bounds_15_29810 : exactInterval 15 29810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29810 : oddCount 29810 15 = 7 ∧ acceleratedOrbit 15 29810 = 1990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29810) = 3 ^ 7 * m + 1990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29810.1, data_15_29810.2]

/-- Complete interval computation for depth 15, residue 29811. -/
theorem bounds_15_29811 : exactInterval 15 29811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29811 : oddCount 29811 15 = 7 ∧ acceleratedOrbit 15 29811 = 1990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29811) = 3 ^ 7 * m + 1990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29811.1, data_15_29811.2]

/-- Complete interval computation for depth 15, residue 29812. -/
theorem bounds_15_29812 : exactInterval 15 29812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29812 : oddCount 29812 15 = 7 ∧ acceleratedOrbit 15 29812 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29812) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29812.1, data_15_29812.2]

/-- Complete interval computation for depth 15, residue 29813. -/
theorem bounds_15_29813 : exactInterval 15 29813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29813 : oddCount 29813 15 = 7 ∧ acceleratedOrbit 15 29813 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29813) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29813.1, data_15_29813.2]

/-- Complete interval computation for depth 15, residue 29814. -/
theorem bounds_15_29814 : exactInterval 15 29814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29814 : oddCount 29814 15 = 7 ∧ acceleratedOrbit 15 29814 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29814) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29814.1, data_15_29814.2]

/-- Complete interval computation for depth 15, residue 29815. -/
theorem bounds_15_29815 : exactInterval 15 29815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29815 : oddCount 29815 15 = 7 ∧ acceleratedOrbit 15 29815 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29815) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29815.1, data_15_29815.2]

/-- Complete interval computation for depth 15, residue 29816. -/
theorem bounds_15_29816 : exactInterval 15 29816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29816 : oddCount 29816 15 = 7 ∧ acceleratedOrbit 15 29816 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29816) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29816.1, data_15_29816.2]

/-- Complete interval computation for depth 15, residue 29817. -/
theorem bounds_15_29817 : exactInterval 15 29817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29817 : oddCount 29817 15 = 9 ∧ acceleratedOrbit 15 29817 = 17912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29817) = 3 ^ 9 * m + 17912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29817.1, data_15_29817.2]

end Collatz.Research.PassageAtlas.Batch0910
