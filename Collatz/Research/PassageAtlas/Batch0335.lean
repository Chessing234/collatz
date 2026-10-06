import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0335

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10944. -/
theorem bounds_15_10944 : exactInterval 15 10944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10944 : oddCount 10944 15 = 5 ∧ acceleratedOrbit 15 10944 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10944) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10944.1, data_15_10944.2]

/-- Complete interval computation for depth 15, residue 10945. -/
theorem bounds_15_10945 : exactInterval 15 10945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10945 : oddCount 10945 15 = 6 ∧ acceleratedOrbit 15 10945 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10945) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10945.1, data_15_10945.2]

/-- Complete interval computation for depth 15, residue 10946. -/
theorem bounds_15_10946 : exactInterval 15 10946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10946 : oddCount 10946 15 = 7 ∧ acceleratedOrbit 15 10946 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10946) = 3 ^ 7 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10946.1, data_15_10946.2]

/-- Complete interval computation for depth 15, residue 10947. -/
theorem bounds_15_10947 : exactInterval 15 10947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10947 : oddCount 10947 15 = 7 ∧ acceleratedOrbit 15 10947 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10947) = 3 ^ 7 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10947.1, data_15_10947.2]

/-- Complete interval computation for depth 15, residue 10948. -/
theorem bounds_15_10948 : exactInterval 15 10948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10948 : oddCount 10948 15 = 6 ∧ acceleratedOrbit 15 10948 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10948) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10948.1, data_15_10948.2]

/-- Complete interval computation for depth 15, residue 10949. -/
theorem bounds_15_10949 : exactInterval 15 10949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10949 : oddCount 10949 15 = 6 ∧ acceleratedOrbit 15 10949 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10949) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10949.1, data_15_10949.2]

/-- Complete interval computation for depth 15, residue 10950. -/
theorem bounds_15_10950 : exactInterval 15 10950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10950 : oddCount 10950 15 = 6 ∧ acceleratedOrbit 15 10950 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10950) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10950.1, data_15_10950.2]

/-- Complete interval computation for depth 15, residue 10951. -/
theorem bounds_15_10951 : exactInterval 15 10951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10951 : oddCount 10951 15 = 9 ∧ acceleratedOrbit 15 10951 = 6581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10951) = 3 ^ 9 * m + 6581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10951.1, data_15_10951.2]

/-- Complete interval computation for depth 15, residue 10952. -/
theorem bounds_15_10952 : exactInterval 15 10952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10952 : oddCount 10952 15 = 6 ∧ acceleratedOrbit 15 10952 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10952) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10952.1, data_15_10952.2]

/-- Complete interval computation for depth 15, residue 10953. -/
theorem bounds_15_10953 : exactInterval 15 10953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10953 : oddCount 10953 15 = 6 ∧ acceleratedOrbit 15 10953 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10953) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10953.1, data_15_10953.2]

/-- Complete interval computation for depth 15, residue 10954. -/
theorem bounds_15_10954 : exactInterval 15 10954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10954 : oddCount 10954 15 = 6 ∧ acceleratedOrbit 15 10954 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10954) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10954.1, data_15_10954.2]

/-- Complete interval computation for depth 15, residue 10955. -/
theorem bounds_15_10955 : exactInterval 15 10955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10955 : oddCount 10955 15 = 8 ∧ acceleratedOrbit 15 10955 = 2195 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10955) = 3 ^ 8 * m + 2195 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10955.1, data_15_10955.2]

/-- Complete interval computation for depth 15, residue 10956. -/
theorem bounds_15_10956 : exactInterval 15 10956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10956 : oddCount 10956 15 = 6 ∧ acceleratedOrbit 15 10956 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10956) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10956.1, data_15_10956.2]

/-- Complete interval computation for depth 15, residue 10957. -/
theorem bounds_15_10957 : exactInterval 15 10957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10957 : oddCount 10957 15 = 6 ∧ acceleratedOrbit 15 10957 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10957) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10957.1, data_15_10957.2]

/-- Complete interval computation for depth 15, residue 10958. -/
theorem bounds_15_10958 : exactInterval 15 10958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10958 : oddCount 10958 15 = 11 ∧ acceleratedOrbit 15 10958 = 59255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10958) = 3 ^ 11 * m + 59255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10958.1, data_15_10958.2]

/-- Complete interval computation for depth 15, residue 10959. -/
theorem bounds_15_10959 : exactInterval 15 10959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10959 : oddCount 10959 15 = 11 ∧ acceleratedOrbit 15 10959 = 59255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10959) = 3 ^ 11 * m + 59255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10959.1, data_15_10959.2]

/-- Complete interval computation for depth 15, residue 10960. -/
theorem bounds_15_10960 : exactInterval 15 10960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10960 : oddCount 10960 15 = 5 ∧ acceleratedOrbit 15 10960 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10960) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10960.1, data_15_10960.2]

/-- Complete interval computation for depth 15, residue 10961. -/
theorem bounds_15_10961 : exactInterval 15 10961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10961 : oddCount 10961 15 = 6 ∧ acceleratedOrbit 15 10961 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10961) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10961.1, data_15_10961.2]

/-- Complete interval computation for depth 15, residue 10962. -/
theorem bounds_15_10962 : exactInterval 15 10962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10962 : oddCount 10962 15 = 6 ∧ acceleratedOrbit 15 10962 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10962) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10962.1, data_15_10962.2]

/-- Complete interval computation for depth 15, residue 10963. -/
theorem bounds_15_10963 : exactInterval 15 10963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10963 : oddCount 10963 15 = 6 ∧ acceleratedOrbit 15 10963 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10963) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10963.1, data_15_10963.2]

/-- Complete interval computation for depth 15, residue 10964. -/
theorem bounds_15_10964 : exactInterval 15 10964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10964 : oddCount 10964 15 = 5 ∧ acceleratedOrbit 15 10964 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10964) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10964.1, data_15_10964.2]

/-- Complete interval computation for depth 15, residue 10965. -/
theorem bounds_15_10965 : exactInterval 15 10965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10965 : oddCount 10965 15 = 5 ∧ acceleratedOrbit 15 10965 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10965) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10965.1, data_15_10965.2]

/-- Complete interval computation for depth 15, residue 10966. -/
theorem bounds_15_10966 : exactInterval 15 10966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10966 : oddCount 10966 15 = 8 ∧ acceleratedOrbit 15 10966 = 2197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10966) = 3 ^ 8 * m + 2197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10966.1, data_15_10966.2]

/-- Complete interval computation for depth 15, residue 10967. -/
theorem bounds_15_10967 : exactInterval 15 10967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10967 : oddCount 10967 15 = 8 ∧ acceleratedOrbit 15 10967 = 2197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10967) = 3 ^ 8 * m + 2197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10967.1, data_15_10967.2]

/-- Complete interval computation for depth 15, residue 10968. -/
theorem bounds_15_10968 : exactInterval 15 10968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10968 : oddCount 10968 15 = 7 ∧ acceleratedOrbit 15 10968 = 733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10968) = 3 ^ 7 * m + 733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10968.1, data_15_10968.2]

/-- Complete interval computation for depth 15, residue 10969. -/
theorem bounds_15_10969 : exactInterval 15 10969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10969 : oddCount 10969 15 = 6 ∧ acceleratedOrbit 15 10969 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10969) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10969.1, data_15_10969.2]

/-- Complete interval computation for depth 15, residue 10970. -/
theorem bounds_15_10970 : exactInterval 15 10970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10970 : oddCount 10970 15 = 7 ∧ acceleratedOrbit 15 10970 = 733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10970) = 3 ^ 7 * m + 733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10970.1, data_15_10970.2]

/-- Complete interval computation for depth 15, residue 10971. -/
theorem bounds_15_10971 : exactInterval 15 10971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10971 : oddCount 10971 15 = 10 ∧ acceleratedOrbit 15 10971 = 19774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10971) = 3 ^ 10 * m + 19774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10971.1, data_15_10971.2]

/-- Complete interval computation for depth 15, residue 10972. -/
theorem bounds_15_10972 : exactInterval 15 10972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10972 : oddCount 10972 15 = 7 ∧ acceleratedOrbit 15 10972 = 733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10972) = 3 ^ 7 * m + 733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10972.1, data_15_10972.2]

/-- Complete interval computation for depth 15, residue 10973. -/
theorem bounds_15_10973 : exactInterval 15 10973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10973 : oddCount 10973 15 = 7 ∧ acceleratedOrbit 15 10973 = 733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10973) = 3 ^ 7 * m + 733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10973.1, data_15_10973.2]

/-- Complete interval computation for depth 15, residue 10974. -/
theorem bounds_15_10974 : exactInterval 15 10974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10974 : oddCount 10974 15 = 8 ∧ acceleratedOrbit 15 10974 = 2198 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10974) = 3 ^ 8 * m + 2198 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10974.1, data_15_10974.2]

/-- Complete interval computation for depth 15, residue 10975. -/
theorem bounds_15_10975 : exactInterval 15 10975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10975 : oddCount 10975 15 = 8 ∧ acceleratedOrbit 15 10975 = 2198 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10975) = 3 ^ 8 * m + 2198 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10975.1, data_15_10975.2]

/-- Complete interval computation for depth 15, residue 10976. -/
theorem bounds_15_10976 : exactInterval 15 10976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10976 : oddCount 10976 15 = 5 ∧ acceleratedOrbit 15 10976 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10976) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10976.1, data_15_10976.2]

end Collatz.Research.PassageAtlas.Batch0335
