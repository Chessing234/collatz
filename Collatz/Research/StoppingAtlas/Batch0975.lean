import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0975

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7792. -/
theorem bounds_13_7792 : exactInterval 13 7792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7792 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7792) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7792 : oddCount 7792 13 = 6 ∧ acceleratedOrbit 13 7792 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7792 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7792) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7792.1, data_13_7792.2]

/-- Complete interval computation for depth 13, residue 7793. -/
theorem bounds_13_7793 : exactInterval 13 7793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7793 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7793) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7793 : oddCount 7793 13 = 5 ∧ acceleratedOrbit 13 7793 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7793 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7793) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7793.1, data_13_7793.2]

/-- Complete interval computation for depth 13, residue 7794. -/
theorem bounds_13_7794 : exactInterval 13 7794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7794 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7794) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7794 : oddCount 7794 13 = 6 ∧ acceleratedOrbit 13 7794 = 694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7794 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7794) = 3 ^ 6 * m + 694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7794.1, data_13_7794.2]

/-- Complete interval computation for depth 13, residue 7795. -/
theorem bounds_13_7795 : exactInterval 13 7795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7795 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7795) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7795 : oddCount 7795 13 = 6 ∧ acceleratedOrbit 13 7795 = 694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7795 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7795) = 3 ^ 6 * m + 694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7795.1, data_13_7795.2]

/-- Complete interval computation for depth 13, residue 7796. -/
theorem bounds_13_7796 : exactInterval 13 7796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7796 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7796) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7796 : oddCount 7796 13 = 6 ∧ acceleratedOrbit 13 7796 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7796 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7796) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7796.1, data_13_7796.2]

/-- Complete interval computation for depth 13, residue 7797. -/
theorem bounds_13_7797 : exactInterval 13 7797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7797 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7797) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7797 : oddCount 7797 13 = 6 ∧ acceleratedOrbit 13 7797 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7797 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7797) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7797.1, data_13_7797.2]

/-- Complete interval computation for depth 13, residue 7798. -/
theorem bounds_13_7798 : exactInterval 13 7798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7798 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7798) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7798 : oddCount 7798 13 = 6 ∧ acceleratedOrbit 13 7798 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7798 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7798) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7798.1, data_13_7798.2]

/-- Complete interval computation for depth 13, residue 7799. -/
theorem bounds_13_7799 : exactInterval 13 7799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7799 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7799) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7799 : oddCount 7799 13 = 6 ∧ acceleratedOrbit 13 7799 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7799 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7799) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7799.1, data_13_7799.2]

/-- Complete interval computation for depth 13, residue 7800. -/
theorem bounds_13_7800 : exactInterval 13 7800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7800 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7800) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7800 : oddCount 7800 13 = 6 ∧ acceleratedOrbit 13 7800 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7800 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7800) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7800.1, data_13_7800.2]

/-- Complete interval computation for depth 13, residue 7801. -/
theorem bounds_13_7801 : exactInterval 13 7801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7801 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7801) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7801 : oddCount 7801 13 = 8 ∧ acceleratedOrbit 13 7801 = 6250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7801 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7801) = 3 ^ 8 * m + 6250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7801.1, data_13_7801.2]

/-- Complete interval computation for depth 13, residue 7802. -/
theorem bounds_13_7802 : exactInterval 13 7802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7802 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7802) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7802 : oddCount 7802 13 = 6 ∧ acceleratedOrbit 13 7802 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7802 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7802) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7802.1, data_13_7802.2]

/-- Complete interval computation for depth 13, residue 7803. -/
theorem bounds_13_7803 : exactInterval 13 7803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7803 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7803) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7803 : oddCount 7803 13 = 6 ∧ acceleratedOrbit 13 7803 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7803 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7803) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7803.1, data_13_7803.2]

/-- Complete interval computation for depth 13, residue 7804. -/
theorem bounds_13_7804 : exactInterval 13 7804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7804 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7804) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7804 : oddCount 7804 13 = 8 ∧ acceleratedOrbit 13 7804 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7804 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7804) = 3 ^ 8 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7804.1, data_13_7804.2]

/-- Complete interval computation for depth 13, residue 7805. -/
theorem bounds_13_7805 : exactInterval 13 7805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7805 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7805) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7805 : oddCount 7805 13 = 8 ∧ acceleratedOrbit 13 7805 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7805 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7805) = 3 ^ 8 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7805.1, data_13_7805.2]

/-- Complete interval computation for depth 13, residue 7806. -/
theorem bounds_13_7806 : exactInterval 13 7806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7806 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7806) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7806 : oddCount 7806 13 = 8 ∧ acceleratedOrbit 13 7806 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7806 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7806) = 3 ^ 8 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7806.1, data_13_7806.2]

/-- Complete interval computation for depth 13, residue 7807. -/
theorem bounds_13_7807 : exactInterval 13 7807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7807 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7807) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7807 : oddCount 7807 13 = 11 ∧ acceleratedOrbit 13 7807 = 168844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7807 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7807) = 3 ^ 11 * m + 168844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7807.1, data_13_7807.2]

end Collatz.Research.StoppingAtlas.Batch0975
