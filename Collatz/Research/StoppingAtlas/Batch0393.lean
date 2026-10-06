import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0393

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2949. -/
theorem bounds_12_2949 : exactInterval 12 2949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2949 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2949) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2949 : oddCount 2949 12 = 7 ∧ acceleratedOrbit 12 2949 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2949 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2949) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2949.1, data_12_2949.2]

/-- Complete interval computation for depth 12, residue 2950. -/
theorem bounds_12_2950 : exactInterval 12 2950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2950 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2950) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2950 : oddCount 2950 12 = 7 ∧ acceleratedOrbit 12 2950 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2950 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2950) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2950.1, data_12_2950.2]

/-- Complete interval computation for depth 12, residue 2951. -/
theorem bounds_12_2951 : exactInterval 12 2951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2951 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2951) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2951 : oddCount 2951 12 = 6 ∧ acceleratedOrbit 12 2951 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2951 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2951) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2951.1, data_12_2951.2]

/-- Complete interval computation for depth 12, residue 2952. -/
theorem bounds_12_2952 : exactInterval 12 2952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2952 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2952) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2952 : oddCount 2952 12 = 3 ∧ acceleratedOrbit 12 2952 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2952 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2952) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2952.1, data_12_2952.2]

/-- Complete interval computation for depth 12, residue 2953. -/
theorem bounds_12_2953 : exactInterval 12 2953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2953 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2953) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2953 : oddCount 2953 12 = 9 ∧ acceleratedOrbit 12 2953 = 14201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2953 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2953) = 3 ^ 9 * m + 14201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2953.1, data_12_2953.2]

/-- Complete interval computation for depth 12, residue 2954. -/
theorem bounds_12_2954 : exactInterval 12 2954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2954 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2954) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2954 : oddCount 2954 12 = 3 ∧ acceleratedOrbit 12 2954 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2954 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2954) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2954.1, data_12_2954.2]

/-- Complete interval computation for depth 12, residue 2955. -/
theorem bounds_12_2955 : exactInterval 12 2955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2955 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2955) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2955 : oddCount 2955 12 = 8 ∧ acceleratedOrbit 12 2955 = 4738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2955 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2955) = 3 ^ 8 * m + 4738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2955.1, data_12_2955.2]

/-- Complete interval computation for depth 12, residue 2956. -/
theorem bounds_12_2956 : exactInterval 12 2956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2956 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2956) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2956 : oddCount 2956 12 = 3 ∧ acceleratedOrbit 12 2956 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2956 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2956) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2956.1, data_12_2956.2]

/-- Complete interval computation for depth 12, residue 2957. -/
theorem bounds_12_2957 : exactInterval 12 2957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2957 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2957) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2957 : oddCount 2957 12 = 3 ∧ acceleratedOrbit 12 2957 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2957 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2957) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2957.1, data_12_2957.2]

/-- Complete interval computation for depth 12, residue 2958. -/
theorem bounds_12_2958 : exactInterval 12 2958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2958 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2958) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2958 : oddCount 2958 12 = 6 ∧ acceleratedOrbit 12 2958 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2958 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2958) = 3 ^ 6 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2958.1, data_12_2958.2]

/-- Complete interval computation for depth 12, residue 2959. -/
theorem bounds_12_2959 : exactInterval 12 2959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2959 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2959) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2959 : oddCount 2959 12 = 6 ∧ acceleratedOrbit 12 2959 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2959 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2959) = 3 ^ 6 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2959.1, data_12_2959.2]

/-- Complete interval computation for depth 12, residue 2960. -/
theorem bounds_12_2960 : exactInterval 12 2960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2960 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2960) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2960 : oddCount 2960 12 = 4 ∧ acceleratedOrbit 12 2960 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2960 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2960) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2960.1, data_12_2960.2]

/-- Complete interval computation for depth 12, residue 2961. -/
theorem bounds_12_2961 : exactInterval 12 2961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2961 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2961) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2961 : oddCount 2961 12 = 5 ∧ acceleratedOrbit 12 2961 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2961 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2961) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2961.1, data_12_2961.2]

/-- Complete interval computation for depth 12, residue 2962. -/
theorem bounds_12_2962 : exactInterval 12 2962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2962 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2962) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2962 : oddCount 2962 12 = 5 ∧ acceleratedOrbit 12 2962 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2962 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2962) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2962.1, data_12_2962.2]

/-- Complete interval computation for depth 12, residue 2963. -/
theorem bounds_12_2963 : exactInterval 12 2963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2963 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2963) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2963 : oddCount 2963 12 = 5 ∧ acceleratedOrbit 12 2963 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2963 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2963) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2963.1, data_12_2963.2]

end Collatz.Research.StoppingAtlas.Batch0393
