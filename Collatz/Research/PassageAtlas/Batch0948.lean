import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0948

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31031. -/
theorem bounds_15_31031 : exactInterval 15 31031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31031 : oddCount 31031 15 = 9 ∧ acceleratedOrbit 15 31031 = 18641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31031) = 3 ^ 9 * m + 18641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31031.1, data_15_31031.2]

/-- Complete interval computation for depth 15, residue 31032. -/
theorem bounds_15_31032 : exactInterval 15 31032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31032 : oddCount 31032 15 = 7 ∧ acceleratedOrbit 15 31032 = 2072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31032) = 3 ^ 7 * m + 2072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31032.1, data_15_31032.2]

/-- Complete interval computation for depth 15, residue 31033. -/
theorem bounds_15_31033 : exactInterval 15 31033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31033 : oddCount 31033 15 = 9 ∧ acceleratedOrbit 15 31033 = 18643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31033) = 3 ^ 9 * m + 18643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31033.1, data_15_31033.2]

/-- Complete interval computation for depth 15, residue 31034. -/
theorem bounds_15_31034 : exactInterval 15 31034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31034 : oddCount 31034 15 = 7 ∧ acceleratedOrbit 15 31034 = 2072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31034) = 3 ^ 7 * m + 2072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31034.1, data_15_31034.2]

/-- Complete interval computation for depth 15, residue 31035. -/
theorem bounds_15_31035 : exactInterval 15 31035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31035 : oddCount 31035 15 = 7 ∧ acceleratedOrbit 15 31035 = 2072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31035) = 3 ^ 7 * m + 2072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31035.1, data_15_31035.2]

/-- Complete interval computation for depth 15, residue 31036. -/
theorem bounds_15_31036 : exactInterval 15 31036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31036 : oddCount 31036 15 = 7 ∧ acceleratedOrbit 15 31036 = 2072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31036) = 3 ^ 7 * m + 2072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31036.1, data_15_31036.2]

/-- Complete interval computation for depth 15, residue 31037. -/
theorem bounds_15_31037 : exactInterval 15 31037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31037 : oddCount 31037 15 = 7 ∧ acceleratedOrbit 15 31037 = 2072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31037) = 3 ^ 7 * m + 2072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31037.1, data_15_31037.2]

/-- Complete interval computation for depth 15, residue 31038. -/
theorem bounds_15_31038 : exactInterval 15 31038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31038 : oddCount 31038 15 = 11 ∧ acceleratedOrbit 15 31038 = 167807 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31038) = 3 ^ 11 * m + 167807 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31038.1, data_15_31038.2]

/-- Complete interval computation for depth 15, residue 31039. -/
theorem bounds_15_31039 : exactInterval 15 31039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31039 : oddCount 31039 15 = 11 ∧ acceleratedOrbit 15 31039 = 167807 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31039) = 3 ^ 11 * m + 167807 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31039.1, data_15_31039.2]

/-- Complete interval computation for depth 15, residue 31040. -/
theorem bounds_15_31040 : exactInterval 15 31040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31040 : oddCount 31040 15 = 5 ∧ acceleratedOrbit 15 31040 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31040) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31040.1, data_15_31040.2]

/-- Complete interval computation for depth 15, residue 31041. -/
theorem bounds_15_31041 : exactInterval 15 31041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31041 : oddCount 31041 15 = 6 ∧ acceleratedOrbit 15 31041 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31041) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31041.1, data_15_31041.2]

/-- Complete interval computation for depth 15, residue 31042. -/
theorem bounds_15_31042 : exactInterval 15 31042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31042 : oddCount 31042 15 = 9 ∧ acceleratedOrbit 15 31042 = 18650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31042) = 3 ^ 9 * m + 18650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31042.1, data_15_31042.2]

/-- Complete interval computation for depth 15, residue 31043. -/
theorem bounds_15_31043 : exactInterval 15 31043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31043 : oddCount 31043 15 = 9 ∧ acceleratedOrbit 15 31043 = 18650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31043) = 3 ^ 9 * m + 18650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31043.1, data_15_31043.2]

/-- Complete interval computation for depth 15, residue 31044. -/
theorem bounds_15_31044 : exactInterval 15 31044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31044 : oddCount 31044 15 = 6 ∧ acceleratedOrbit 15 31044 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31044) = 3 ^ 6 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31044.1, data_15_31044.2]

/-- Complete interval computation for depth 15, residue 31045. -/
theorem bounds_15_31045 : exactInterval 15 31045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31045 : oddCount 31045 15 = 6 ∧ acceleratedOrbit 15 31045 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31045) = 3 ^ 6 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31045.1, data_15_31045.2]

/-- Complete interval computation for depth 15, residue 31046. -/
theorem bounds_15_31046 : exactInterval 15 31046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31046 : oddCount 31046 15 = 6 ∧ acceleratedOrbit 15 31046 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31046) = 3 ^ 6 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31046.1, data_15_31046.2]

/-- Complete interval computation for depth 15, residue 31047. -/
theorem bounds_15_31047 : exactInterval 15 31047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31047 : oddCount 31047 15 = 11 ∧ acceleratedOrbit 15 31047 = 167852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31047) = 3 ^ 11 * m + 167852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31047.1, data_15_31047.2]

/-- Complete interval computation for depth 15, residue 31048. -/
theorem bounds_15_31048 : exactInterval 15 31048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31048 : oddCount 31048 15 = 6 ∧ acceleratedOrbit 15 31048 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31048) = 3 ^ 6 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31048.1, data_15_31048.2]

/-- Complete interval computation for depth 15, residue 31049. -/
theorem bounds_15_31049 : exactInterval 15 31049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31049 : oddCount 31049 15 = 8 ∧ acceleratedOrbit 15 31049 = 6218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31049) = 3 ^ 8 * m + 6218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31049.1, data_15_31049.2]

/-- Complete interval computation for depth 15, residue 31050. -/
theorem bounds_15_31050 : exactInterval 15 31050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31050 : oddCount 31050 15 = 6 ∧ acceleratedOrbit 15 31050 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31050) = 3 ^ 6 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31050.1, data_15_31050.2]

/-- Complete interval computation for depth 15, residue 31051. -/
theorem bounds_15_31051 : exactInterval 15 31051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31051 : oddCount 31051 15 = 6 ∧ acceleratedOrbit 15 31051 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31051) = 3 ^ 6 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31051.1, data_15_31051.2]

/-- Complete interval computation for depth 15, residue 31052. -/
theorem bounds_15_31052 : exactInterval 15 31052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31052 : oddCount 31052 15 = 6 ∧ acceleratedOrbit 15 31052 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31052) = 3 ^ 6 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31052.1, data_15_31052.2]

/-- Complete interval computation for depth 15, residue 31053. -/
theorem bounds_15_31053 : exactInterval 15 31053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31053 : oddCount 31053 15 = 6 ∧ acceleratedOrbit 15 31053 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31053) = 3 ^ 6 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31053.1, data_15_31053.2]

/-- Complete interval computation for depth 15, residue 31054. -/
theorem bounds_15_31054 : exactInterval 15 31054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31054 : oddCount 31054 15 = 10 ∧ acceleratedOrbit 15 31054 = 55966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31054) = 3 ^ 10 * m + 55966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31054.1, data_15_31054.2]

/-- Complete interval computation for depth 15, residue 31055. -/
theorem bounds_15_31055 : exactInterval 15 31055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31055 : oddCount 31055 15 = 10 ∧ acceleratedOrbit 15 31055 = 55966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31055) = 3 ^ 10 * m + 55966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31055.1, data_15_31055.2]

/-- Complete interval computation for depth 15, residue 31056. -/
theorem bounds_15_31056 : exactInterval 15 31056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31056 : oddCount 31056 15 = 5 ∧ acceleratedOrbit 15 31056 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31056) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31056.1, data_15_31056.2]

/-- Complete interval computation for depth 15, residue 31057. -/
theorem bounds_15_31057 : exactInterval 15 31057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31057 : oddCount 31057 15 = 9 ∧ acceleratedOrbit 15 31057 = 18658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31057) = 3 ^ 9 * m + 18658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31057.1, data_15_31057.2]

/-- Complete interval computation for depth 15, residue 31058. -/
theorem bounds_15_31058 : exactInterval 15 31058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31058 : oddCount 31058 15 = 9 ∧ acceleratedOrbit 15 31058 = 18658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31058) = 3 ^ 9 * m + 18658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31058.1, data_15_31058.2]

/-- Complete interval computation for depth 15, residue 31059. -/
theorem bounds_15_31059 : exactInterval 15 31059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31059 : oddCount 31059 15 = 9 ∧ acceleratedOrbit 15 31059 = 18658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31059) = 3 ^ 9 * m + 18658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31059.1, data_15_31059.2]

/-- Complete interval computation for depth 15, residue 31060. -/
theorem bounds_15_31060 : exactInterval 15 31060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31060 : oddCount 31060 15 = 5 ∧ acceleratedOrbit 15 31060 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31060) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31060.1, data_15_31060.2]

/-- Complete interval computation for depth 15, residue 31061. -/
theorem bounds_15_31061 : exactInterval 15 31061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31061 : oddCount 31061 15 = 5 ∧ acceleratedOrbit 15 31061 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31061) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31061.1, data_15_31061.2]

/-- Complete interval computation for depth 15, residue 31062. -/
theorem bounds_15_31062 : exactInterval 15 31062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31062 : oddCount 31062 15 = 7 ∧ acceleratedOrbit 15 31062 = 2074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31062) = 3 ^ 7 * m + 2074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31062.1, data_15_31062.2]

/-- Complete interval computation for depth 15, residue 31063. -/
theorem bounds_15_31063 : exactInterval 15 31063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31063 : oddCount 31063 15 = 7 ∧ acceleratedOrbit 15 31063 = 2074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31063) = 3 ^ 7 * m + 2074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31063.1, data_15_31063.2]

end Collatz.Research.PassageAtlas.Batch0948
