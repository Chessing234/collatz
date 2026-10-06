import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0987

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7976. -/
theorem bounds_13_7976 : exactInterval 13 7976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7976 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7976) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7976 : oddCount 7976 13 = 5 ∧ acceleratedOrbit 13 7976 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7976 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7976) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7976.1, data_13_7976.2]

/-- Complete interval computation for depth 13, residue 7977. -/
theorem bounds_13_7977 : exactInterval 13 7977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7977 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7977) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7977 : oddCount 7977 13 = 6 ∧ acceleratedOrbit 13 7977 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7977 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7977) = 3 ^ 6 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7977.1, data_13_7977.2]

/-- Complete interval computation for depth 13, residue 7978. -/
theorem bounds_13_7978 : exactInterval 13 7978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7978 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7978) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7978 : oddCount 7978 13 = 5 ∧ acceleratedOrbit 13 7978 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7978 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7978) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7978.1, data_13_7978.2]

/-- Complete interval computation for depth 13, residue 7979. -/
theorem bounds_13_7979 : exactInterval 13 7979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7979 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7979) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7979 : oddCount 7979 13 = 7 ∧ acceleratedOrbit 13 7979 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7979 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7979) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7979.1, data_13_7979.2]

/-- Complete interval computation for depth 13, residue 7980. -/
theorem bounds_13_7980 : exactInterval 13 7980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7980 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7980) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7980 : oddCount 7980 13 = 4 ∧ acceleratedOrbit 13 7980 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7980 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7980) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7980.1, data_13_7980.2]

/-- Complete interval computation for depth 13, residue 7981. -/
theorem bounds_13_7981 : exactInterval 13 7981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7981 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7981) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7981 : oddCount 7981 13 = 4 ∧ acceleratedOrbit 13 7981 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7981 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7981) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7981.1, data_13_7981.2]

/-- Complete interval computation for depth 13, residue 7982. -/
theorem bounds_13_7982 : exactInterval 13 7982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7982 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7982) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7982 : oddCount 7982 13 = 4 ∧ acceleratedOrbit 13 7982 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7982 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7982) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7982.1, data_13_7982.2]

/-- Complete interval computation for depth 13, residue 7983. -/
theorem bounds_13_7983 : exactInterval 13 7983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7983 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7983) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7983 : oddCount 7983 13 = 7 ∧ acceleratedOrbit 13 7983 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7983 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7983) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7983.1, data_13_7983.2]

/-- Complete interval computation for depth 13, residue 7984. -/
theorem bounds_13_7984 : exactInterval 13 7984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7984 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7984) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7984 : oddCount 7984 13 = 5 ∧ acceleratedOrbit 13 7984 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7984 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7984) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7984.1, data_13_7984.2]

/-- Complete interval computation for depth 13, residue 7985. -/
theorem bounds_13_7985 : exactInterval 13 7985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7985 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7985) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7985 : oddCount 7985 13 = 4 ∧ acceleratedOrbit 13 7985 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7985 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7985) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7985.1, data_13_7985.2]

/-- Complete interval computation for depth 13, residue 7986. -/
theorem bounds_13_7986 : exactInterval 13 7986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7986 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7986) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7986 : oddCount 7986 13 = 4 ∧ acceleratedOrbit 13 7986 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7986 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7986) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7986.1, data_13_7986.2]

/-- Complete interval computation for depth 13, residue 7987. -/
theorem bounds_13_7987 : exactInterval 13 7987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7987 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7987) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7987 : oddCount 7987 13 = 4 ∧ acceleratedOrbit 13 7987 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7987 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7987) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7987.1, data_13_7987.2]

/-- Complete interval computation for depth 13, residue 7988. -/
theorem bounds_13_7988 : exactInterval 13 7988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7988 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7988) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7988 : oddCount 7988 13 = 5 ∧ acceleratedOrbit 13 7988 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7988 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7988) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7988.1, data_13_7988.2]

/-- Complete interval computation for depth 13, residue 7989. -/
theorem bounds_13_7989 : exactInterval 13 7989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7989 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7989) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7989 : oddCount 7989 13 = 5 ∧ acceleratedOrbit 13 7989 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7989 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7989) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7989.1, data_13_7989.2]

/-- Complete interval computation for depth 13, residue 7990. -/
theorem bounds_13_7990 : exactInterval 13 7990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7990 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7990) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7990 : oddCount 7990 13 = 7 ∧ acceleratedOrbit 13 7990 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7990 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7990) = 3 ^ 7 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7990.1, data_13_7990.2]

/-- Complete interval computation for depth 13, residue 7991. -/
theorem bounds_13_7991 : exactInterval 13 7991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7991 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7991) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7991 : oddCount 7991 13 = 7 ∧ acceleratedOrbit 13 7991 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7991 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7991) = 3 ^ 7 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7991.1, data_13_7991.2]

end Collatz.Research.StoppingAtlas.Batch0987
