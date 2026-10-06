import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0239

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7798. -/
theorem bounds_15_7798 : exactInterval 15 7798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7798 : oddCount 7798 15 = 8 ∧ acceleratedOrbit 15 7798 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7798) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7798.1, data_15_7798.2]

/-- Complete interval computation for depth 15, residue 7799. -/
theorem bounds_15_7799 : exactInterval 15 7799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7799 : oddCount 7799 15 = 8 ∧ acceleratedOrbit 15 7799 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7799) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7799.1, data_15_7799.2]

/-- Complete interval computation for depth 15, residue 7800. -/
theorem bounds_15_7800 : exactInterval 15 7800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7800 : oddCount 7800 15 = 8 ∧ acceleratedOrbit 15 7800 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7800) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7800.1, data_15_7800.2]

/-- Complete interval computation for depth 15, residue 7801. -/
theorem bounds_15_7801 : exactInterval 15 7801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7801 : oddCount 7801 15 = 9 ∧ acceleratedOrbit 15 7801 = 4688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7801) = 3 ^ 9 * m + 4688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7801.1, data_15_7801.2]

/-- Complete interval computation for depth 15, residue 7802. -/
theorem bounds_15_7802 : exactInterval 15 7802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7802 : oddCount 7802 15 = 8 ∧ acceleratedOrbit 15 7802 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7802) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7802.1, data_15_7802.2]

/-- Complete interval computation for depth 15, residue 7803. -/
theorem bounds_15_7803 : exactInterval 15 7803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7803 : oddCount 7803 15 = 8 ∧ acceleratedOrbit 15 7803 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7803) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7803.1, data_15_7803.2]

/-- Complete interval computation for depth 15, residue 7804. -/
theorem bounds_15_7804 : exactInterval 15 7804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7804 : oddCount 7804 15 = 9 ∧ acceleratedOrbit 15 7804 = 4691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7804) = 3 ^ 9 * m + 4691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7804.1, data_15_7804.2]

/-- Complete interval computation for depth 15, residue 7805. -/
theorem bounds_15_7805 : exactInterval 15 7805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7805 : oddCount 7805 15 = 9 ∧ acceleratedOrbit 15 7805 = 4691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7805) = 3 ^ 9 * m + 4691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7805.1, data_15_7805.2]

/-- Complete interval computation for depth 15, residue 7806. -/
theorem bounds_15_7806 : exactInterval 15 7806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7806 : oddCount 7806 15 = 9 ∧ acceleratedOrbit 15 7806 = 4691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7806) = 3 ^ 9 * m + 4691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7806.1, data_15_7806.2]

/-- Complete interval computation for depth 15, residue 7807. -/
theorem bounds_15_7807 : exactInterval 15 7807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7807 : oddCount 7807 15 = 11 ∧ acceleratedOrbit 15 7807 = 42211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7807) = 3 ^ 11 * m + 42211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7807.1, data_15_7807.2]

/-- Complete interval computation for depth 15, residue 7808. -/
theorem bounds_15_7808 : exactInterval 15 7808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7808 : oddCount 7808 15 = 4 ∧ acceleratedOrbit 15 7808 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7808) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7808.1, data_15_7808.2]

/-- Complete interval computation for depth 15, residue 7809. -/
theorem bounds_15_7809 : exactInterval 15 7809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7809 : oddCount 7809 15 = 9 ∧ acceleratedOrbit 15 7809 = 4693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7809) = 3 ^ 9 * m + 4693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7809.1, data_15_7809.2]

/-- Complete interval computation for depth 15, residue 7810. -/
theorem bounds_15_7810 : exactInterval 15 7810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7810 : oddCount 7810 15 = 6 ∧ acceleratedOrbit 15 7810 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7810) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7810.1, data_15_7810.2]

/-- Complete interval computation for depth 15, residue 7811. -/
theorem bounds_15_7811 : exactInterval 15 7811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7811 : oddCount 7811 15 = 6 ∧ acceleratedOrbit 15 7811 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7811) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7811.1, data_15_7811.2]

/-- Complete interval computation for depth 15, residue 7812. -/
theorem bounds_15_7812 : exactInterval 15 7812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7812 : oddCount 7812 15 = 5 ∧ acceleratedOrbit 15 7812 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7812) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7812.1, data_15_7812.2]

/-- Complete interval computation for depth 15, residue 7813. -/
theorem bounds_15_7813 : exactInterval 15 7813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7813 : oddCount 7813 15 = 5 ∧ acceleratedOrbit 15 7813 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7813) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7813.1, data_15_7813.2]

/-- Complete interval computation for depth 15, residue 7814. -/
theorem bounds_15_7814 : exactInterval 15 7814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7814 : oddCount 7814 15 = 5 ∧ acceleratedOrbit 15 7814 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7814) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7814.1, data_15_7814.2]

/-- Complete interval computation for depth 15, residue 7815. -/
theorem bounds_15_7815 : exactInterval 15 7815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7815 : oddCount 7815 15 = 10 ∧ acceleratedOrbit 15 7815 = 14093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7815) = 3 ^ 10 * m + 14093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7815.1, data_15_7815.2]

/-- Complete interval computation for depth 15, residue 7816. -/
theorem bounds_15_7816 : exactInterval 15 7816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7816 : oddCount 7816 15 = 6 ∧ acceleratedOrbit 15 7816 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7816) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7816.1, data_15_7816.2]

/-- Complete interval computation for depth 15, residue 7817. -/
theorem bounds_15_7817 : exactInterval 15 7817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7817 : oddCount 7817 15 = 11 ∧ acceleratedOrbit 15 7817 = 42272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7817) = 3 ^ 11 * m + 42272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7817.1, data_15_7817.2]

/-- Complete interval computation for depth 15, residue 7818. -/
theorem bounds_15_7818 : exactInterval 15 7818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7818 : oddCount 7818 15 = 6 ∧ acceleratedOrbit 15 7818 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7818) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7818.1, data_15_7818.2]

/-- Complete interval computation for depth 15, residue 7819. -/
theorem bounds_15_7819 : exactInterval 15 7819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7819 : oddCount 7819 15 = 5 ∧ acceleratedOrbit 15 7819 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7819) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7819.1, data_15_7819.2]

/-- Complete interval computation for depth 15, residue 7820. -/
theorem bounds_15_7820 : exactInterval 15 7820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7820 : oddCount 7820 15 = 6 ∧ acceleratedOrbit 15 7820 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7820) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7820.1, data_15_7820.2]

/-- Complete interval computation for depth 15, residue 7821. -/
theorem bounds_15_7821 : exactInterval 15 7821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7821 : oddCount 7821 15 = 6 ∧ acceleratedOrbit 15 7821 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7821) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7821.1, data_15_7821.2]

/-- Complete interval computation for depth 15, residue 7822. -/
theorem bounds_15_7822 : exactInterval 15 7822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7822 : oddCount 7822 15 = 8 ∧ acceleratedOrbit 15 7822 = 1567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7822) = 3 ^ 8 * m + 1567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7822.1, data_15_7822.2]

/-- Complete interval computation for depth 15, residue 7823. -/
theorem bounds_15_7823 : exactInterval 15 7823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7823 : oddCount 7823 15 = 8 ∧ acceleratedOrbit 15 7823 = 1567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7823) = 3 ^ 8 * m + 1567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7823.1, data_15_7823.2]

/-- Complete interval computation for depth 15, residue 7824. -/
theorem bounds_15_7824 : exactInterval 15 7824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7824 : oddCount 7824 15 = 7 ∧ acceleratedOrbit 15 7824 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7824) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7824.1, data_15_7824.2]

/-- Complete interval computation for depth 15, residue 7825. -/
theorem bounds_15_7825 : exactInterval 15 7825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7825 : oddCount 7825 15 = 7 ∧ acceleratedOrbit 15 7825 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7825) = 3 ^ 7 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7825.1, data_15_7825.2]

/-- Complete interval computation for depth 15, residue 7826. -/
theorem bounds_15_7826 : exactInterval 15 7826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7826 : oddCount 7826 15 = 7 ∧ acceleratedOrbit 15 7826 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7826) = 3 ^ 7 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7826.1, data_15_7826.2]

/-- Complete interval computation for depth 15, residue 7827. -/
theorem bounds_15_7827 : exactInterval 15 7827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7827 : oddCount 7827 15 = 7 ∧ acceleratedOrbit 15 7827 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7827) = 3 ^ 7 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7827.1, data_15_7827.2]

/-- Complete interval computation for depth 15, residue 7828. -/
theorem bounds_15_7828 : exactInterval 15 7828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7828 : oddCount 7828 15 = 7 ∧ acceleratedOrbit 15 7828 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7828) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7828.1, data_15_7828.2]

/-- Complete interval computation for depth 15, residue 7829. -/
theorem bounds_15_7829 : exactInterval 15 7829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7829 : oddCount 7829 15 = 7 ∧ acceleratedOrbit 15 7829 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7829) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7829.1, data_15_7829.2]

/-- Complete interval computation for depth 15, residue 7830. -/
theorem bounds_15_7830 : exactInterval 15 7830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7830 : oddCount 7830 15 = 6 ∧ acceleratedOrbit 15 7830 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7830) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7830.1, data_15_7830.2]

end Collatz.Research.PassageAtlas.Batch0239
