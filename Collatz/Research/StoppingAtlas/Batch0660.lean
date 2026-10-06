import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0660

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2954. -/
theorem bounds_13_2954 : exactInterval 13 2954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2954 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2954) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2954 : oddCount 2954 13 = 3 ∧ acceleratedOrbit 13 2954 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2954 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2954) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2954.1, data_13_2954.2]

/-- Complete interval computation for depth 13, residue 2955. -/
theorem bounds_13_2955 : exactInterval 13 2955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2955 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2955) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2955 : oddCount 2955 13 = 8 ∧ acceleratedOrbit 13 2955 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2955 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2955) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2955.1, data_13_2955.2]

/-- Complete interval computation for depth 13, residue 2956. -/
theorem bounds_13_2956 : exactInterval 13 2956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2956 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2956) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2956 : oddCount 2956 13 = 3 ∧ acceleratedOrbit 13 2956 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2956 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2956) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2956.1, data_13_2956.2]

/-- Complete interval computation for depth 13, residue 2957. -/
theorem bounds_13_2957 : exactInterval 13 2957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2957 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2957) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2957 : oddCount 2957 13 = 3 ∧ acceleratedOrbit 13 2957 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2957 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2957) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2957.1, data_13_2957.2]

/-- Complete interval computation for depth 13, residue 2958. -/
theorem bounds_13_2958 : exactInterval 13 2958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2958 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2958) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2958 : oddCount 2958 13 = 7 ∧ acceleratedOrbit 13 2958 = 791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2958 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2958) = 3 ^ 7 * m + 791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2958.1, data_13_2958.2]

/-- Complete interval computation for depth 13, residue 2959. -/
theorem bounds_13_2959 : exactInterval 13 2959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2959 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2959) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2959 : oddCount 2959 13 = 7 ∧ acceleratedOrbit 13 2959 = 791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2959 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2959) = 3 ^ 7 * m + 791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2959.1, data_13_2959.2]

/-- Complete interval computation for depth 13, residue 2960. -/
theorem bounds_13_2960 : exactInterval 13 2960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2960 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2960) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2960 : oddCount 2960 13 = 5 ∧ acceleratedOrbit 13 2960 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2960 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2960) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2960.1, data_13_2960.2]

/-- Complete interval computation for depth 13, residue 2961. -/
theorem bounds_13_2961 : exactInterval 13 2961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2961 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2961) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2961 : oddCount 2961 13 = 5 ∧ acceleratedOrbit 13 2961 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2961 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2961) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2961.1, data_13_2961.2]

/-- Complete interval computation for depth 13, residue 2962. -/
theorem bounds_13_2962 : exactInterval 13 2962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2962 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2962) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2962 : oddCount 2962 13 = 5 ∧ acceleratedOrbit 13 2962 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2962 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2962) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2962.1, data_13_2962.2]

/-- Complete interval computation for depth 13, residue 2963. -/
theorem bounds_13_2963 : exactInterval 13 2963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2963 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2963) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2963 : oddCount 2963 13 = 5 ∧ acceleratedOrbit 13 2963 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2963 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2963) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2963.1, data_13_2963.2]

/-- Complete interval computation for depth 13, residue 2964. -/
theorem bounds_13_2964 : exactInterval 13 2964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2964 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2964) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2964 : oddCount 2964 13 = 5 ∧ acceleratedOrbit 13 2964 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2964 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2964) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2964.1, data_13_2964.2]

/-- Complete interval computation for depth 13, residue 2965. -/
theorem bounds_13_2965 : exactInterval 13 2965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2965 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2965) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2965 : oddCount 2965 13 = 5 ∧ acceleratedOrbit 13 2965 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2965 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2965) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2965.1, data_13_2965.2]

/-- Complete interval computation for depth 13, residue 2966. -/
theorem bounds_13_2966 : exactInterval 13 2966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2966 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2966) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2966 : oddCount 2966 13 = 6 ∧ acceleratedOrbit 13 2966 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2966 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2966) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2966.1, data_13_2966.2]

/-- Complete interval computation for depth 13, residue 2967. -/
theorem bounds_13_2967 : exactInterval 13 2967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2967 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2967) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2967 : oddCount 2967 13 = 6 ∧ acceleratedOrbit 13 2967 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2967 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2967) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2967.1, data_13_2967.2]

/-- Complete interval computation for depth 13, residue 2968. -/
theorem bounds_13_2968 : exactInterval 13 2968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2968 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2968) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2968 : oddCount 2968 13 = 5 ∧ acceleratedOrbit 13 2968 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2968 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2968) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2968.1, data_13_2968.2]

end Collatz.Research.StoppingAtlas.Batch0660
