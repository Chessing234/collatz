import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0333

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2027. -/
theorem bounds_12_2027 : exactInterval 12 2027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2027 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2027) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2027 : oddCount 2027 12 = 8 ∧ acceleratedOrbit 12 2027 = 3250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2027 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2027) = 3 ^ 8 * m + 3250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2027.1, data_12_2027.2]

/-- Complete interval computation for depth 12, residue 2028. -/
theorem bounds_12_2028 : exactInterval 12 2028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2028 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2028) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2028 : oddCount 2028 12 = 6 ∧ acceleratedOrbit 12 2028 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2028 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2028) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2028.1, data_12_2028.2]

/-- Complete interval computation for depth 12, residue 2029. -/
theorem bounds_12_2029 : exactInterval 12 2029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2029 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2029) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2029 : oddCount 2029 12 = 6 ∧ acceleratedOrbit 12 2029 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2029 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2029) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2029.1, data_12_2029.2]

/-- Complete interval computation for depth 12, residue 2030. -/
theorem bounds_12_2030 : exactInterval 12 2030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2030 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2030) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2030 : oddCount 2030 12 = 6 ∧ acceleratedOrbit 12 2030 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2030 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2030) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2030.1, data_12_2030.2]

/-- Complete interval computation for depth 12, residue 2031. -/
theorem bounds_12_2031 : exactInterval 12 2031 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2031 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2031) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2031 : oddCount 2031 12 = 7 ∧ acceleratedOrbit 12 2031 = 1085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2031 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2031) = 3 ^ 7 * m + 1085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2031.1, data_12_2031.2]

/-- Complete interval computation for depth 12, residue 2032. -/
theorem bounds_12_2032 : exactInterval 12 2032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2032 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2032) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2032 : oddCount 2032 12 = 7 ∧ acceleratedOrbit 12 2032 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2032 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2032) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2032.1, data_12_2032.2]

/-- Complete interval computation for depth 12, residue 2033. -/
theorem bounds_12_2033 : exactInterval 12 2033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2033 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2033) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2033 : oddCount 2033 12 = 6 ∧ acceleratedOrbit 12 2033 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2033 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2033) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2033.1, data_12_2033.2]

/-- Complete interval computation for depth 12, residue 2034. -/
theorem bounds_12_2034 : exactInterval 12 2034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2034 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2034) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2034 : oddCount 2034 12 = 8 ∧ acceleratedOrbit 12 2034 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2034 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2034) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2034.1, data_12_2034.2]

/-- Complete interval computation for depth 12, residue 2035. -/
theorem bounds_12_2035 : exactInterval 12 2035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2035 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2035) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2035 : oddCount 2035 12 = 8 ∧ acceleratedOrbit 12 2035 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2035 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2035) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2035.1, data_12_2035.2]

/-- Complete interval computation for depth 12, residue 2036. -/
theorem bounds_12_2036 : exactInterval 12 2036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2036 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2036) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2036 : oddCount 2036 12 = 7 ∧ acceleratedOrbit 12 2036 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2036 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2036) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2036.1, data_12_2036.2]

/-- Complete interval computation for depth 12, residue 2037. -/
theorem bounds_12_2037 : exactInterval 12 2037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2037 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2037) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2037 : oddCount 2037 12 = 7 ∧ acceleratedOrbit 12 2037 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2037 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2037) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2037.1, data_12_2037.2]

/-- Complete interval computation for depth 12, residue 2038. -/
theorem bounds_12_2038 : exactInterval 12 2038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2038 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2038) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2038 : oddCount 2038 12 = 7 ∧ acceleratedOrbit 12 2038 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2038 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2038) = 3 ^ 7 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2038.1, data_12_2038.2]

/-- Complete interval computation for depth 12, residue 2039. -/
theorem bounds_12_2039 : exactInterval 12 2039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2039 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2039) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2039 : oddCount 2039 12 = 7 ∧ acceleratedOrbit 12 2039 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2039 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2039) = 3 ^ 7 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2039.1, data_12_2039.2]

/-- Complete interval computation for depth 12, residue 2040. -/
theorem bounds_12_2040 : exactInterval 12 2040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2040 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2040) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2040 : oddCount 2040 12 = 8 ∧ acceleratedOrbit 12 2040 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2040 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2040) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2040.1, data_12_2040.2]

/-- Complete interval computation for depth 12, residue 2041. -/
theorem bounds_12_2041 : exactInterval 12 2041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2041 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2041) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2041 : oddCount 2041 12 = 7 ∧ acceleratedOrbit 12 2041 = 1091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2041 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2041) = 3 ^ 7 * m + 1091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2041.1, data_12_2041.2]

end Collatz.Research.StoppingAtlas.Batch0333
