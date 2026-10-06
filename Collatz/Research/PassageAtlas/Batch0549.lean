import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0549

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17956. -/
theorem bounds_15_17956 : exactInterval 15 17956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17956 : oddCount 17956 15 = 7 ∧ acceleratedOrbit 15 17956 = 1199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17956) = 3 ^ 7 * m + 1199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17956.1, data_15_17956.2]

/-- Complete interval computation for depth 15, residue 17957. -/
theorem bounds_15_17957 : exactInterval 15 17957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17957 : oddCount 17957 15 = 7 ∧ acceleratedOrbit 15 17957 = 1199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17957) = 3 ^ 7 * m + 1199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17957.1, data_15_17957.2]

/-- Complete interval computation for depth 15, residue 17958. -/
theorem bounds_15_17958 : exactInterval 15 17958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17958 : oddCount 17958 15 = 7 ∧ acceleratedOrbit 15 17958 = 1199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17958) = 3 ^ 7 * m + 1199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17958.1, data_15_17958.2]

/-- Complete interval computation for depth 15, residue 17959. -/
theorem bounds_15_17959 : exactInterval 15 17959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17959 : oddCount 17959 15 = 7 ∧ acceleratedOrbit 15 17959 = 1199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17959) = 3 ^ 7 * m + 1199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17959.1, data_15_17959.2]

/-- Complete interval computation for depth 15, residue 17960. -/
theorem bounds_15_17960 : exactInterval 15 17960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17960 : oddCount 17960 15 = 6 ∧ acceleratedOrbit 15 17960 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17960) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17960.1, data_15_17960.2]

/-- Complete interval computation for depth 15, residue 17961. -/
theorem bounds_15_17961 : exactInterval 15 17961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17961 : oddCount 17961 15 = 11 ∧ acceleratedOrbit 15 17961 = 97109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17961) = 3 ^ 11 * m + 97109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17961.1, data_15_17961.2]

/-- Complete interval computation for depth 15, residue 17962. -/
theorem bounds_15_17962 : exactInterval 15 17962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17962 : oddCount 17962 15 = 6 ∧ acceleratedOrbit 15 17962 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17962) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17962.1, data_15_17962.2]

/-- Complete interval computation for depth 15, residue 17963. -/
theorem bounds_15_17963 : exactInterval 15 17963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17963 : oddCount 17963 15 = 6 ∧ acceleratedOrbit 15 17963 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17963) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17963.1, data_15_17963.2]

/-- Complete interval computation for depth 15, residue 17964. -/
theorem bounds_15_17964 : exactInterval 15 17964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17964 : oddCount 17964 15 = 9 ∧ acceleratedOrbit 15 17964 = 10799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17964) = 3 ^ 9 * m + 10799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17964.1, data_15_17964.2]

/-- Complete interval computation for depth 15, residue 17965. -/
theorem bounds_15_17965 : exactInterval 15 17965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17965 : oddCount 17965 15 = 9 ∧ acceleratedOrbit 15 17965 = 10799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17965) = 3 ^ 9 * m + 10799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17965.1, data_15_17965.2]

/-- Complete interval computation for depth 15, residue 17966. -/
theorem bounds_15_17966 : exactInterval 15 17966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17966 : oddCount 17966 15 = 9 ∧ acceleratedOrbit 15 17966 = 10799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17966) = 3 ^ 9 * m + 10799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17966.1, data_15_17966.2]

/-- Complete interval computation for depth 15, residue 17967. -/
theorem bounds_15_17967 : exactInterval 15 17967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17967 : oddCount 17967 15 = 11 ∧ acceleratedOrbit 15 17967 = 97139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17967) = 3 ^ 11 * m + 97139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17967.1, data_15_17967.2]

/-- Complete interval computation for depth 15, residue 17968. -/
theorem bounds_15_17968 : exactInterval 15 17968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17968 : oddCount 17968 15 = 6 ∧ acceleratedOrbit 15 17968 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17968) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17968.1, data_15_17968.2]

/-- Complete interval computation for depth 15, residue 17969. -/
theorem bounds_15_17969 : exactInterval 15 17969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17969 : oddCount 17969 15 = 9 ∧ acceleratedOrbit 15 17969 = 10799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17969) = 3 ^ 9 * m + 10799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17969.1, data_15_17969.2]

/-- Complete interval computation for depth 15, residue 17970. -/
theorem bounds_15_17970 : exactInterval 15 17970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17970 : oddCount 17970 15 = 9 ∧ acceleratedOrbit 15 17970 = 10799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17970) = 3 ^ 9 * m + 10799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17970.1, data_15_17970.2]

/-- Complete interval computation for depth 15, residue 17971. -/
theorem bounds_15_17971 : exactInterval 15 17971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17971 : oddCount 17971 15 = 9 ∧ acceleratedOrbit 15 17971 = 10799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17971) = 3 ^ 9 * m + 10799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17971.1, data_15_17971.2]

/-- Complete interval computation for depth 15, residue 17972. -/
theorem bounds_15_17972 : exactInterval 15 17972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17972 : oddCount 17972 15 = 6 ∧ acceleratedOrbit 15 17972 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17972) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17972.1, data_15_17972.2]

/-- Complete interval computation for depth 15, residue 17973. -/
theorem bounds_15_17973 : exactInterval 15 17973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17973 : oddCount 17973 15 = 6 ∧ acceleratedOrbit 15 17973 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17973) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17973.1, data_15_17973.2]

/-- Complete interval computation for depth 15, residue 17974. -/
theorem bounds_15_17974 : exactInterval 15 17974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17974 : oddCount 17974 15 = 10 ∧ acceleratedOrbit 15 17974 = 32395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17974) = 3 ^ 10 * m + 32395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17974.1, data_15_17974.2]

/-- Complete interval computation for depth 15, residue 17975. -/
theorem bounds_15_17975 : exactInterval 15 17975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17975 : oddCount 17975 15 = 10 ∧ acceleratedOrbit 15 17975 = 32395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17975) = 3 ^ 10 * m + 32395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17975.1, data_15_17975.2]

/-- Complete interval computation for depth 15, residue 17976. -/
theorem bounds_15_17976 : exactInterval 15 17976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17976 : oddCount 17976 15 = 7 ∧ acceleratedOrbit 15 17976 = 1201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17976) = 3 ^ 7 * m + 1201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17976.1, data_15_17976.2]

/-- Complete interval computation for depth 15, residue 17977. -/
theorem bounds_15_17977 : exactInterval 15 17977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17977 : oddCount 17977 15 = 6 ∧ acceleratedOrbit 15 17977 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17977) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17977.1, data_15_17977.2]

/-- Complete interval computation for depth 15, residue 17978. -/
theorem bounds_15_17978 : exactInterval 15 17978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17978 : oddCount 17978 15 = 7 ∧ acceleratedOrbit 15 17978 = 1201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17978) = 3 ^ 7 * m + 1201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17978.1, data_15_17978.2]

/-- Complete interval computation for depth 15, residue 17979. -/
theorem bounds_15_17979 : exactInterval 15 17979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17979 : oddCount 17979 15 = 8 ∧ acceleratedOrbit 15 17979 = 3601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17979) = 3 ^ 8 * m + 3601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17979.1, data_15_17979.2]

/-- Complete interval computation for depth 15, residue 17980. -/
theorem bounds_15_17980 : exactInterval 15 17980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17980 : oddCount 17980 15 = 7 ∧ acceleratedOrbit 15 17980 = 1201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17980) = 3 ^ 7 * m + 1201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17980.1, data_15_17980.2]

/-- Complete interval computation for depth 15, residue 17981. -/
theorem bounds_15_17981 : exactInterval 15 17981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17981 : oddCount 17981 15 = 7 ∧ acceleratedOrbit 15 17981 = 1201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17981) = 3 ^ 7 * m + 1201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17981.1, data_15_17981.2]

/-- Complete interval computation for depth 15, residue 17982. -/
theorem bounds_15_17982 : exactInterval 15 17982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17982 : oddCount 17982 15 = 8 ∧ acceleratedOrbit 15 17982 = 3601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17982) = 3 ^ 8 * m + 3601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17982.1, data_15_17982.2]

/-- Complete interval computation for depth 15, residue 17983. -/
theorem bounds_15_17983 : exactInterval 15 17983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17983 : oddCount 17983 15 = 8 ∧ acceleratedOrbit 15 17983 = 3601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17983) = 3 ^ 8 * m + 3601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17983.1, data_15_17983.2]

/-- Complete interval computation for depth 15, residue 17984. -/
theorem bounds_15_17984 : exactInterval 15 17984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17984 : oddCount 17984 15 = 6 ∧ acceleratedOrbit 15 17984 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17984) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17984.1, data_15_17984.2]

/-- Complete interval computation for depth 15, residue 17985. -/
theorem bounds_15_17985 : exactInterval 15 17985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17985 : oddCount 17985 15 = 8 ∧ acceleratedOrbit 15 17985 = 3604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17985) = 3 ^ 8 * m + 3604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17985.1, data_15_17985.2]

/-- Complete interval computation for depth 15, residue 17986. -/
theorem bounds_15_17986 : exactInterval 15 17986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17986 : oddCount 17986 15 = 8 ∧ acceleratedOrbit 15 17986 = 3604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17986) = 3 ^ 8 * m + 3604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17986.1, data_15_17986.2]

/-- Complete interval computation for depth 15, residue 17987. -/
theorem bounds_15_17987 : exactInterval 15 17987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17987 : oddCount 17987 15 = 8 ∧ acceleratedOrbit 15 17987 = 3604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17987) = 3 ^ 8 * m + 3604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17987.1, data_15_17987.2]

/-- Complete interval computation for depth 15, residue 17988. -/
theorem bounds_15_17988 : exactInterval 15 17988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17988 : oddCount 17988 15 = 5 ∧ acceleratedOrbit 15 17988 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17988) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17988.1, data_15_17988.2]

end Collatz.Research.PassageAtlas.Batch0549
