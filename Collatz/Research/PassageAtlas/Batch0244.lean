import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0244

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7962. -/
theorem bounds_15_7962 : exactInterval 15 7962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7962 : oddCount 7962 15 = 4 ∧ acceleratedOrbit 15 7962 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7962) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7962.1, data_15_7962.2]

/-- Complete interval computation for depth 15, residue 7963. -/
theorem bounds_15_7963 : exactInterval 15 7963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7963 : oddCount 7963 15 = 12 ∧ acceleratedOrbit 15 7963 = 129170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7963) = 3 ^ 12 * m + 129170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7963.1, data_15_7963.2]

/-- Complete interval computation for depth 15, residue 7964. -/
theorem bounds_15_7964 : exactInterval 15 7964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7964 : oddCount 7964 15 = 7 ∧ acceleratedOrbit 15 7964 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7964) = 3 ^ 7 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7964.1, data_15_7964.2]

/-- Complete interval computation for depth 15, residue 7965. -/
theorem bounds_15_7965 : exactInterval 15 7965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7965 : oddCount 7965 15 = 7 ∧ acceleratedOrbit 15 7965 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7965) = 3 ^ 7 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7965.1, data_15_7965.2]

/-- Complete interval computation for depth 15, residue 7966. -/
theorem bounds_15_7966 : exactInterval 15 7966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7966 : oddCount 7966 15 = 7 ∧ acceleratedOrbit 15 7966 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7966) = 3 ^ 7 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7966.1, data_15_7966.2]

/-- Complete interval computation for depth 15, residue 7967. -/
theorem bounds_15_7967 : exactInterval 15 7967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7967 : oddCount 7967 15 = 9 ∧ acceleratedOrbit 15 7967 = 4787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7967) = 3 ^ 9 * m + 4787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7967.1, data_15_7967.2]

/-- Complete interval computation for depth 15, residue 7968. -/
theorem bounds_15_7968 : exactInterval 15 7968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7968 : oddCount 7968 15 = 6 ∧ acceleratedOrbit 15 7968 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7968) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7968.1, data_15_7968.2]

/-- Complete interval computation for depth 15, residue 7969. -/
theorem bounds_15_7969 : exactInterval 15 7969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7969 : oddCount 7969 15 = 7 ∧ acceleratedOrbit 15 7969 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7969) = 3 ^ 7 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7969.1, data_15_7969.2]

/-- Complete interval computation for depth 15, residue 7970. -/
theorem bounds_15_7970 : exactInterval 15 7970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7970 : oddCount 7970 15 = 7 ∧ acceleratedOrbit 15 7970 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7970) = 3 ^ 7 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7970.1, data_15_7970.2]

/-- Complete interval computation for depth 15, residue 7971. -/
theorem bounds_15_7971 : exactInterval 15 7971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7971 : oddCount 7971 15 = 7 ∧ acceleratedOrbit 15 7971 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7971) = 3 ^ 7 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7971.1, data_15_7971.2]

/-- Complete interval computation for depth 15, residue 7972. -/
theorem bounds_15_7972 : exactInterval 15 7972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7972 : oddCount 7972 15 = 7 ∧ acceleratedOrbit 15 7972 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7972) = 3 ^ 7 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7972.1, data_15_7972.2]

/-- Complete interval computation for depth 15, residue 7973. -/
theorem bounds_15_7973 : exactInterval 15 7973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7973 : oddCount 7973 15 = 7 ∧ acceleratedOrbit 15 7973 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7973) = 3 ^ 7 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7973.1, data_15_7973.2]

/-- Complete interval computation for depth 15, residue 7974. -/
theorem bounds_15_7974 : exactInterval 15 7974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7974 : oddCount 7974 15 = 7 ∧ acceleratedOrbit 15 7974 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7974) = 3 ^ 7 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7974.1, data_15_7974.2]

/-- Complete interval computation for depth 15, residue 7975. -/
theorem bounds_15_7975 : exactInterval 15 7975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7975 : oddCount 7975 15 = 9 ∧ acceleratedOrbit 15 7975 = 4792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7975) = 3 ^ 9 * m + 4792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7975.1, data_15_7975.2]

/-- Complete interval computation for depth 15, residue 7976. -/
theorem bounds_15_7976 : exactInterval 15 7976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7976 : oddCount 7976 15 = 6 ∧ acceleratedOrbit 15 7976 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7976) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7976.1, data_15_7976.2]

/-- Complete interval computation for depth 15, residue 7977. -/
theorem bounds_15_7977 : exactInterval 15 7977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7977 : oddCount 7977 15 = 7 ∧ acceleratedOrbit 15 7977 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7977) = 3 ^ 7 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7977.1, data_15_7977.2]

/-- Complete interval computation for depth 15, residue 7978. -/
theorem bounds_15_7978 : exactInterval 15 7978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7978 : oddCount 7978 15 = 6 ∧ acceleratedOrbit 15 7978 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7978) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7978.1, data_15_7978.2]

/-- Complete interval computation for depth 15, residue 7979. -/
theorem bounds_15_7979 : exactInterval 15 7979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7979 : oddCount 7979 15 = 7 ∧ acceleratedOrbit 15 7979 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7979) = 3 ^ 7 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7979.1, data_15_7979.2]

/-- Complete interval computation for depth 15, residue 7980. -/
theorem bounds_15_7980 : exactInterval 15 7980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7980 : oddCount 7980 15 = 6 ∧ acceleratedOrbit 15 7980 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7980) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7980.1, data_15_7980.2]

/-- Complete interval computation for depth 15, residue 7981. -/
theorem bounds_15_7981 : exactInterval 15 7981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7981 : oddCount 7981 15 = 6 ∧ acceleratedOrbit 15 7981 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7981) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7981.1, data_15_7981.2]

/-- Complete interval computation for depth 15, residue 7982. -/
theorem bounds_15_7982 : exactInterval 15 7982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7982 : oddCount 7982 15 = 6 ∧ acceleratedOrbit 15 7982 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7982) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7982.1, data_15_7982.2]

/-- Complete interval computation for depth 15, residue 7983. -/
theorem bounds_15_7983 : exactInterval 15 7983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7983 : oddCount 7983 15 = 7 ∧ acceleratedOrbit 15 7983 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7983) = 3 ^ 7 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7983.1, data_15_7983.2]

/-- Complete interval computation for depth 15, residue 7984. -/
theorem bounds_15_7984 : exactInterval 15 7984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7984 : oddCount 7984 15 = 6 ∧ acceleratedOrbit 15 7984 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7984) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7984.1, data_15_7984.2]

/-- Complete interval computation for depth 15, residue 7985. -/
theorem bounds_15_7985 : exactInterval 15 7985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7985 : oddCount 7985 15 = 6 ∧ acceleratedOrbit 15 7985 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7985) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7985.1, data_15_7985.2]

/-- Complete interval computation for depth 15, residue 7986. -/
theorem bounds_15_7986 : exactInterval 15 7986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7986 : oddCount 7986 15 = 6 ∧ acceleratedOrbit 15 7986 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7986) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7986.1, data_15_7986.2]

/-- Complete interval computation for depth 15, residue 7987. -/
theorem bounds_15_7987 : exactInterval 15 7987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7987 : oddCount 7987 15 = 6 ∧ acceleratedOrbit 15 7987 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7987) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7987.1, data_15_7987.2]

/-- Complete interval computation for depth 15, residue 7988. -/
theorem bounds_15_7988 : exactInterval 15 7988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7988 : oddCount 7988 15 = 6 ∧ acceleratedOrbit 15 7988 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7988) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7988.1, data_15_7988.2]

/-- Complete interval computation for depth 15, residue 7989. -/
theorem bounds_15_7989 : exactInterval 15 7989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7989 : oddCount 7989 15 = 6 ∧ acceleratedOrbit 15 7989 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7989) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7989.1, data_15_7989.2]

/-- Complete interval computation for depth 15, residue 7990. -/
theorem bounds_15_7990 : exactInterval 15 7990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7990 : oddCount 7990 15 = 8 ∧ acceleratedOrbit 15 7990 = 1601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7990) = 3 ^ 8 * m + 1601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7990.1, data_15_7990.2]

/-- Complete interval computation for depth 15, residue 7991. -/
theorem bounds_15_7991 : exactInterval 15 7991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7991 : oddCount 7991 15 = 8 ∧ acceleratedOrbit 15 7991 = 1601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7991) = 3 ^ 8 * m + 1601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7991.1, data_15_7991.2]

/-- Complete interval computation for depth 15, residue 7992. -/
theorem bounds_15_7992 : exactInterval 15 7992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7992 : oddCount 7992 15 = 6 ∧ acceleratedOrbit 15 7992 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7992) = 3 ^ 6 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7992.1, data_15_7992.2]

/-- Complete interval computation for depth 15, residue 7993. -/
theorem bounds_15_7993 : exactInterval 15 7993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7993 : oddCount 7993 15 = 9 ∧ acceleratedOrbit 15 7993 = 4805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7993) = 3 ^ 9 * m + 4805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7993.1, data_15_7993.2]

/-- Complete interval computation for depth 15, residue 7994. -/
theorem bounds_15_7994 : exactInterval 15 7994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7994 : oddCount 7994 15 = 6 ∧ acceleratedOrbit 15 7994 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7994) = 3 ^ 6 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7994.1, data_15_7994.2]

end Collatz.Research.PassageAtlas.Batch0244
