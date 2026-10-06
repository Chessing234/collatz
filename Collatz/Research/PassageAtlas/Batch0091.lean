import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0091

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2949. -/
theorem bounds_15_2949 : exactInterval 15 2949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2949 : oddCount 2949 15 = 9 ∧ acceleratedOrbit 15 2949 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2949) = 3 ^ 9 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2949.1, data_15_2949.2]

/-- Complete interval computation for depth 15, residue 2950. -/
theorem bounds_15_2950 : exactInterval 15 2950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2950 : oddCount 2950 15 = 9 ∧ acceleratedOrbit 15 2950 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2950) = 3 ^ 9 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2950.1, data_15_2950.2]

/-- Complete interval computation for depth 15, residue 2951. -/
theorem bounds_15_2951 : exactInterval 15 2951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2951 : oddCount 2951 15 = 8 ∧ acceleratedOrbit 15 2951 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2951) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2951.1, data_15_2951.2]

/-- Complete interval computation for depth 15, residue 2952. -/
theorem bounds_15_2952 : exactInterval 15 2952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2952 : oddCount 2952 15 = 4 ∧ acceleratedOrbit 15 2952 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2952) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2952.1, data_15_2952.2]

/-- Complete interval computation for depth 15, residue 2953. -/
theorem bounds_15_2953 : exactInterval 15 2953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2953 : oddCount 2953 15 = 11 ∧ acceleratedOrbit 15 2953 = 15977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2953) = 3 ^ 11 * m + 15977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2953.1, data_15_2953.2]

/-- Complete interval computation for depth 15, residue 2954. -/
theorem bounds_15_2954 : exactInterval 15 2954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2954 : oddCount 2954 15 = 4 ∧ acceleratedOrbit 15 2954 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2954) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2954.1, data_15_2954.2]

/-- Complete interval computation for depth 15, residue 2955. -/
theorem bounds_15_2955 : exactInterval 15 2955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2955 : oddCount 2955 15 = 9 ∧ acceleratedOrbit 15 2955 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2955) = 3 ^ 9 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2955.1, data_15_2955.2]

/-- Complete interval computation for depth 15, residue 2956. -/
theorem bounds_15_2956 : exactInterval 15 2956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2956 : oddCount 2956 15 = 4 ∧ acceleratedOrbit 15 2956 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2956) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2956.1, data_15_2956.2]

/-- Complete interval computation for depth 15, residue 2957. -/
theorem bounds_15_2957 : exactInterval 15 2957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2957 : oddCount 2957 15 = 4 ∧ acceleratedOrbit 15 2957 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2957) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2957.1, data_15_2957.2]

/-- Complete interval computation for depth 15, residue 2958. -/
theorem bounds_15_2958 : exactInterval 15 2958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2958 : oddCount 2958 15 = 9 ∧ acceleratedOrbit 15 2958 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2958) = 3 ^ 9 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2958.1, data_15_2958.2]

/-- Complete interval computation for depth 15, residue 2959. -/
theorem bounds_15_2959 : exactInterval 15 2959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2959 : oddCount 2959 15 = 9 ∧ acceleratedOrbit 15 2959 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2959) = 3 ^ 9 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2959.1, data_15_2959.2]

/-- Complete interval computation for depth 15, residue 2960. -/
theorem bounds_15_2960 : exactInterval 15 2960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2960 : oddCount 2960 15 = 6 ∧ acceleratedOrbit 15 2960 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2960) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2960.1, data_15_2960.2]

/-- Complete interval computation for depth 15, residue 2961. -/
theorem bounds_15_2961 : exactInterval 15 2961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2961 : oddCount 2961 15 = 5 ∧ acceleratedOrbit 15 2961 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2961) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2961.1, data_15_2961.2]

/-- Complete interval computation for depth 15, residue 2962. -/
theorem bounds_15_2962 : exactInterval 15 2962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2962 : oddCount 2962 15 = 5 ∧ acceleratedOrbit 15 2962 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2962) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2962.1, data_15_2962.2]

/-- Complete interval computation for depth 15, residue 2963. -/
theorem bounds_15_2963 : exactInterval 15 2963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2963 : oddCount 2963 15 = 5 ∧ acceleratedOrbit 15 2963 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2963) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2963.1, data_15_2963.2]

/-- Complete interval computation for depth 15, residue 2964. -/
theorem bounds_15_2964 : exactInterval 15 2964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2964 : oddCount 2964 15 = 6 ∧ acceleratedOrbit 15 2964 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2964) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2964.1, data_15_2964.2]

/-- Complete interval computation for depth 15, residue 2965. -/
theorem bounds_15_2965 : exactInterval 15 2965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2965 : oddCount 2965 15 = 6 ∧ acceleratedOrbit 15 2965 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2965) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2965.1, data_15_2965.2]

/-- Complete interval computation for depth 15, residue 2966. -/
theorem bounds_15_2966 : exactInterval 15 2966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2966 : oddCount 2966 15 = 7 ∧ acceleratedOrbit 15 2966 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2966) = 3 ^ 7 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2966.1, data_15_2966.2]

/-- Complete interval computation for depth 15, residue 2967. -/
theorem bounds_15_2967 : exactInterval 15 2967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2967 : oddCount 2967 15 = 7 ∧ acceleratedOrbit 15 2967 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2967) = 3 ^ 7 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2967.1, data_15_2967.2]

/-- Complete interval computation for depth 15, residue 2968. -/
theorem bounds_15_2968 : exactInterval 15 2968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2968 : oddCount 2968 15 = 6 ∧ acceleratedOrbit 15 2968 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2968) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2968.1, data_15_2968.2]

/-- Complete interval computation for depth 15, residue 2969. -/
theorem bounds_15_2969 : exactInterval 15 2969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2969 : oddCount 2969 15 = 7 ∧ acceleratedOrbit 15 2969 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2969) = 3 ^ 7 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2969.1, data_15_2969.2]

/-- Complete interval computation for depth 15, residue 2970. -/
theorem bounds_15_2970 : exactInterval 15 2970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2970 : oddCount 2970 15 = 6 ∧ acceleratedOrbit 15 2970 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2970) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2970.1, data_15_2970.2]

/-- Complete interval computation for depth 15, residue 2971. -/
theorem bounds_15_2971 : exactInterval 15 2971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2971 : oddCount 2971 15 = 8 ∧ acceleratedOrbit 15 2971 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2971) = 3 ^ 8 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2971.1, data_15_2971.2]

/-- Complete interval computation for depth 15, residue 2972. -/
theorem bounds_15_2972 : exactInterval 15 2972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2972 : oddCount 2972 15 = 10 ∧ acceleratedOrbit 15 2972 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2972) = 3 ^ 10 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2972.1, data_15_2972.2]

/-- Complete interval computation for depth 15, residue 2973. -/
theorem bounds_15_2973 : exactInterval 15 2973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2973 : oddCount 2973 15 = 10 ∧ acceleratedOrbit 15 2973 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2973) = 3 ^ 10 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2973.1, data_15_2973.2]

/-- Complete interval computation for depth 15, residue 2974. -/
theorem bounds_15_2974 : exactInterval 15 2974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2974 : oddCount 2974 15 = 10 ∧ acceleratedOrbit 15 2974 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2974) = 3 ^ 10 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2974.1, data_15_2974.2]

/-- Complete interval computation for depth 15, residue 2975. -/
theorem bounds_15_2975 : exactInterval 15 2975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2975 : oddCount 2975 15 = 8 ∧ acceleratedOrbit 15 2975 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2975) = 3 ^ 8 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2975.1, data_15_2975.2]

/-- Complete interval computation for depth 15, residue 2976. -/
theorem bounds_15_2976 : exactInterval 15 2976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2976 : oddCount 2976 15 = 4 ∧ acceleratedOrbit 15 2976 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2976) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2976.1, data_15_2976.2]

/-- Complete interval computation for depth 15, residue 2977. -/
theorem bounds_15_2977 : exactInterval 15 2977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2977 : oddCount 2977 15 = 7 ∧ acceleratedOrbit 15 2977 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2977) = 3 ^ 7 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2977.1, data_15_2977.2]

/-- Complete interval computation for depth 15, residue 2978. -/
theorem bounds_15_2978 : exactInterval 15 2978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2978 : oddCount 2978 15 = 6 ∧ acceleratedOrbit 15 2978 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2978) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2978.1, data_15_2978.2]

/-- Complete interval computation for depth 15, residue 2979. -/
theorem bounds_15_2979 : exactInterval 15 2979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2979 : oddCount 2979 15 = 6 ∧ acceleratedOrbit 15 2979 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2979) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2979.1, data_15_2979.2]

/-- Complete interval computation for depth 15, residue 2980. -/
theorem bounds_15_2980 : exactInterval 15 2980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2980 : oddCount 2980 15 = 9 ∧ acceleratedOrbit 15 2980 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2980) = 3 ^ 9 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2980.1, data_15_2980.2]

end Collatz.Research.PassageAtlas.Batch0091
