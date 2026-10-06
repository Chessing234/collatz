import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0925

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7024. -/
theorem bounds_13_7024 : exactInterval 13 7024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7024 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7024) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7024 : oddCount 7024 13 = 5 ∧ acceleratedOrbit 13 7024 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7024 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7024) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7024.1, data_13_7024.2]

/-- Complete interval computation for depth 13, residue 7025. -/
theorem bounds_13_7025 : exactInterval 13 7025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7025 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7025) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7025 : oddCount 7025 13 = 5 ∧ acceleratedOrbit 13 7025 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7025 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7025) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7025.1, data_13_7025.2]

/-- Complete interval computation for depth 13, residue 7026. -/
theorem bounds_13_7026 : exactInterval 13 7026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7026 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7026) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7026 : oddCount 7026 13 = 5 ∧ acceleratedOrbit 13 7026 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7026 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7026) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7026.1, data_13_7026.2]

/-- Complete interval computation for depth 13, residue 7027. -/
theorem bounds_13_7027 : exactInterval 13 7027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7027 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7027) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7027 : oddCount 7027 13 = 5 ∧ acceleratedOrbit 13 7027 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7027 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7027) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7027.1, data_13_7027.2]

/-- Complete interval computation for depth 13, residue 7028. -/
theorem bounds_13_7028 : exactInterval 13 7028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7028 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7028) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7028 : oddCount 7028 13 = 5 ∧ acceleratedOrbit 13 7028 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7028 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7028) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7028.1, data_13_7028.2]

/-- Complete interval computation for depth 13, residue 7029. -/
theorem bounds_13_7029 : exactInterval 13 7029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7029 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7029) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7029 : oddCount 7029 13 = 5 ∧ acceleratedOrbit 13 7029 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7029 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7029) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7029.1, data_13_7029.2]

/-- Complete interval computation for depth 13, residue 7030. -/
theorem bounds_13_7030 : exactInterval 13 7030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7030 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7030) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7030 : oddCount 7030 13 = 6 ∧ acceleratedOrbit 13 7030 = 626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7030 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7030) = 3 ^ 6 * m + 626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7030.1, data_13_7030.2]

/-- Complete interval computation for depth 13, residue 7031. -/
theorem bounds_13_7031 : exactInterval 13 7031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7031 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7031) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7031 : oddCount 7031 13 = 6 ∧ acceleratedOrbit 13 7031 = 626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7031 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7031) = 3 ^ 6 * m + 626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7031.1, data_13_7031.2]

/-- Complete interval computation for depth 13, residue 7032. -/
theorem bounds_13_7032 : exactInterval 13 7032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7032 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7032) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7032 : oddCount 7032 13 = 7 ∧ acceleratedOrbit 13 7032 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7032 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7032) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7032.1, data_13_7032.2]

/-- Complete interval computation for depth 13, residue 7033. -/
theorem bounds_13_7033 : exactInterval 13 7033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7033 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7033) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7033 : oddCount 7033 13 = 9 ∧ acceleratedOrbit 13 7033 = 16904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7033 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7033) = 3 ^ 9 * m + 16904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7033.1, data_13_7033.2]

/-- Complete interval computation for depth 13, residue 7034. -/
theorem bounds_13_7034 : exactInterval 13 7034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7034 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7034) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7034 : oddCount 7034 13 = 7 ∧ acceleratedOrbit 13 7034 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7034 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7034) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7034.1, data_13_7034.2]

/-- Complete interval computation for depth 13, residue 7035. -/
theorem bounds_13_7035 : exactInterval 13 7035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7035 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7035) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7035 : oddCount 7035 13 = 8 ∧ acceleratedOrbit 13 7035 = 5636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7035 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7035) = 3 ^ 8 * m + 5636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7035.1, data_13_7035.2]

/-- Complete interval computation for depth 13, residue 7036. -/
theorem bounds_13_7036 : exactInterval 13 7036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7036 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7036) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7036 : oddCount 7036 13 = 7 ∧ acceleratedOrbit 13 7036 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7036 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7036) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7036.1, data_13_7036.2]

/-- Complete interval computation for depth 13, residue 7037. -/
theorem bounds_13_7037 : exactInterval 13 7037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7037 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7037) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7037 : oddCount 7037 13 = 7 ∧ acceleratedOrbit 13 7037 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7037 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7037) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7037.1, data_13_7037.2]

/-- Complete interval computation for depth 13, residue 7038. -/
theorem bounds_13_7038 : exactInterval 13 7038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7038 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7038) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7038 : oddCount 7038 13 = 10 ∧ acceleratedOrbit 13 7038 = 50746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7038 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7038) = 3 ^ 10 * m + 50746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7038.1, data_13_7038.2]

/-- Complete interval computation for depth 13, residue 7039. -/
theorem bounds_13_7039 : exactInterval 13 7039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7039 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7039) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7039 : oddCount 7039 13 = 10 ∧ acceleratedOrbit 13 7039 = 50746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7039 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7039) = 3 ^ 10 * m + 50746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7039.1, data_13_7039.2]

end Collatz.Research.StoppingAtlas.Batch0925
