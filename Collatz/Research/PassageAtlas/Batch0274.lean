import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0274

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8945. -/
theorem bounds_15_8945 : exactInterval 15 8945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8945 : oddCount 8945 15 = 5 ∧ acceleratedOrbit 15 8945 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8945) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8945.1, data_15_8945.2]

/-- Complete interval computation for depth 15, residue 8946. -/
theorem bounds_15_8946 : exactInterval 15 8946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8946 : oddCount 8946 15 = 10 ∧ acceleratedOrbit 15 8946 = 16129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8946) = 3 ^ 10 * m + 16129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8946.1, data_15_8946.2]

/-- Complete interval computation for depth 15, residue 8947. -/
theorem bounds_15_8947 : exactInterval 15 8947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8947 : oddCount 8947 15 = 10 ∧ acceleratedOrbit 15 8947 = 16129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8947) = 3 ^ 10 * m + 16129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8947.1, data_15_8947.2]

/-- Complete interval computation for depth 15, residue 8948. -/
theorem bounds_15_8948 : exactInterval 15 8948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8948 : oddCount 8948 15 = 8 ∧ acceleratedOrbit 15 8948 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8948) = 3 ^ 8 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8948.1, data_15_8948.2]

/-- Complete interval computation for depth 15, residue 8949. -/
theorem bounds_15_8949 : exactInterval 15 8949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8949 : oddCount 8949 15 = 8 ∧ acceleratedOrbit 15 8949 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8949) = 3 ^ 8 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8949.1, data_15_8949.2]

/-- Complete interval computation for depth 15, residue 8950. -/
theorem bounds_15_8950 : exactInterval 15 8950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8950 : oddCount 8950 15 = 8 ∧ acceleratedOrbit 15 8950 = 1793 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8950) = 3 ^ 8 * m + 1793 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8950.1, data_15_8950.2]

/-- Complete interval computation for depth 15, residue 8951. -/
theorem bounds_15_8951 : exactInterval 15 8951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8951 : oddCount 8951 15 = 8 ∧ acceleratedOrbit 15 8951 = 1793 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8951) = 3 ^ 8 * m + 1793 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8951.1, data_15_8951.2]

/-- Complete interval computation for depth 15, residue 8952. -/
theorem bounds_15_8952 : exactInterval 15 8952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8952 : oddCount 8952 15 = 8 ∧ acceleratedOrbit 15 8952 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8952) = 3 ^ 8 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8952.1, data_15_8952.2]

/-- Complete interval computation for depth 15, residue 8953. -/
theorem bounds_15_8953 : exactInterval 15 8953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8953 : oddCount 8953 15 = 7 ∧ acceleratedOrbit 15 8953 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8953) = 3 ^ 7 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8953.1, data_15_8953.2]

/-- Complete interval computation for depth 15, residue 8954. -/
theorem bounds_15_8954 : exactInterval 15 8954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8954 : oddCount 8954 15 = 8 ∧ acceleratedOrbit 15 8954 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8954) = 3 ^ 8 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8954.1, data_15_8954.2]

/-- Complete interval computation for depth 15, residue 8955. -/
theorem bounds_15_8955 : exactInterval 15 8955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8955 : oddCount 8955 15 = 10 ∧ acceleratedOrbit 15 8955 = 16141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8955) = 3 ^ 10 * m + 16141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8955.1, data_15_8955.2]

/-- Complete interval computation for depth 15, residue 8956. -/
theorem bounds_15_8956 : exactInterval 15 8956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8956 : oddCount 8956 15 = 7 ∧ acceleratedOrbit 15 8956 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8956) = 3 ^ 7 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8956.1, data_15_8956.2]

/-- Complete interval computation for depth 15, residue 8957. -/
theorem bounds_15_8957 : exactInterval 15 8957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8957 : oddCount 8957 15 = 7 ∧ acceleratedOrbit 15 8957 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8957) = 3 ^ 7 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8957.1, data_15_8957.2]

/-- Complete interval computation for depth 15, residue 8958. -/
theorem bounds_15_8958 : exactInterval 15 8958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8958 : oddCount 8958 15 = 7 ∧ acceleratedOrbit 15 8958 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8958) = 3 ^ 7 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8958.1, data_15_8958.2]

/-- Complete interval computation for depth 15, residue 8959. -/
theorem bounds_15_8959 : exactInterval 15 8959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8959 : oddCount 8959 15 = 11 ∧ acceleratedOrbit 15 8959 = 48439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8959) = 3 ^ 11 * m + 48439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8959.1, data_15_8959.2]

/-- Complete interval computation for depth 15, residue 8960. -/
theorem bounds_15_8960 : exactInterval 15 8960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8960 : oddCount 8960 15 = 3 ∧ acceleratedOrbit 15 8960 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8960) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8960.1, data_15_8960.2]

/-- Complete interval computation for depth 15, residue 8961. -/
theorem bounds_15_8961 : exactInterval 15 8961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8961 : oddCount 8961 15 = 6 ∧ acceleratedOrbit 15 8961 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8961) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8961.1, data_15_8961.2]

/-- Complete interval computation for depth 15, residue 8962. -/
theorem bounds_15_8962 : exactInterval 15 8962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8962 : oddCount 8962 15 = 6 ∧ acceleratedOrbit 15 8962 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8962) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8962.1, data_15_8962.2]

/-- Complete interval computation for depth 15, residue 8963. -/
theorem bounds_15_8963 : exactInterval 15 8963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8963 : oddCount 8963 15 = 6 ∧ acceleratedOrbit 15 8963 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8963) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8963.1, data_15_8963.2]

/-- Complete interval computation for depth 15, residue 8964. -/
theorem bounds_15_8964 : exactInterval 15 8964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8964 : oddCount 8964 15 = 6 ∧ acceleratedOrbit 15 8964 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8964) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8964.1, data_15_8964.2]

/-- Complete interval computation for depth 15, residue 8965. -/
theorem bounds_15_8965 : exactInterval 15 8965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8965 : oddCount 8965 15 = 6 ∧ acceleratedOrbit 15 8965 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8965) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8965.1, data_15_8965.2]

/-- Complete interval computation for depth 15, residue 8966. -/
theorem bounds_15_8966 : exactInterval 15 8966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8966 : oddCount 8966 15 = 6 ∧ acceleratedOrbit 15 8966 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8966) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8966.1, data_15_8966.2]

/-- Complete interval computation for depth 15, residue 8967. -/
theorem bounds_15_8967 : exactInterval 15 8967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8967 : oddCount 8967 15 = 8 ∧ acceleratedOrbit 15 8967 = 1796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8967) = 3 ^ 8 * m + 1796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8967.1, data_15_8967.2]

/-- Complete interval computation for depth 15, residue 8968. -/
theorem bounds_15_8968 : exactInterval 15 8968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8968 : oddCount 8968 15 = 6 ∧ acceleratedOrbit 15 8968 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8968) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8968.1, data_15_8968.2]

/-- Complete interval computation for depth 15, residue 8969. -/
theorem bounds_15_8969 : exactInterval 15 8969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8969 : oddCount 8969 15 = 9 ∧ acceleratedOrbit 15 8969 = 5390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8969) = 3 ^ 9 * m + 5390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8969.1, data_15_8969.2]

/-- Complete interval computation for depth 15, residue 8970. -/
theorem bounds_15_8970 : exactInterval 15 8970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8970 : oddCount 8970 15 = 6 ∧ acceleratedOrbit 15 8970 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8970) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8970.1, data_15_8970.2]

/-- Complete interval computation for depth 15, residue 8971. -/
theorem bounds_15_8971 : exactInterval 15 8971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8971 : oddCount 8971 15 = 7 ∧ acceleratedOrbit 15 8971 = 599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8971) = 3 ^ 7 * m + 599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8971.1, data_15_8971.2]

/-- Complete interval computation for depth 15, residue 8972. -/
theorem bounds_15_8972 : exactInterval 15 8972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8972 : oddCount 8972 15 = 6 ∧ acceleratedOrbit 15 8972 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8972) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8972.1, data_15_8972.2]

/-- Complete interval computation for depth 15, residue 8973. -/
theorem bounds_15_8973 : exactInterval 15 8973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8973 : oddCount 8973 15 = 6 ∧ acceleratedOrbit 15 8973 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8973) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8973.1, data_15_8973.2]

/-- Complete interval computation for depth 15, residue 8974. -/
theorem bounds_15_8974 : exactInterval 15 8974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8974 : oddCount 8974 15 = 6 ∧ acceleratedOrbit 15 8974 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8974) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8974.1, data_15_8974.2]

/-- Complete interval computation for depth 15, residue 8975. -/
theorem bounds_15_8975 : exactInterval 15 8975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8975 : oddCount 8975 15 = 6 ∧ acceleratedOrbit 15 8975 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8975) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8975.1, data_15_8975.2]

/-- Complete interval computation for depth 15, residue 8976. -/
theorem bounds_15_8976 : exactInterval 15 8976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8976 : oddCount 8976 15 = 6 ∧ acceleratedOrbit 15 8976 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8976) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8976.1, data_15_8976.2]

/-- Complete interval computation for depth 15, residue 8977. -/
theorem bounds_15_8977 : exactInterval 15 8977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8977 : oddCount 8977 15 = 6 ∧ acceleratedOrbit 15 8977 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8977) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8977.1, data_15_8977.2]

end Collatz.Research.PassageAtlas.Batch0274
