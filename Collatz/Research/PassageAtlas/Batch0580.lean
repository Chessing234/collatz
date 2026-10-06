import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0580

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18972. -/
theorem bounds_15_18972 : exactInterval 15 18972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18972 : oddCount 18972 15 = 7 ∧ acceleratedOrbit 15 18972 = 1268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18972) = 3 ^ 7 * m + 1268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18972.1, data_15_18972.2]

/-- Complete interval computation for depth 15, residue 18973. -/
theorem bounds_15_18973 : exactInterval 15 18973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18973 : oddCount 18973 15 = 7 ∧ acceleratedOrbit 15 18973 = 1268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18973) = 3 ^ 7 * m + 1268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18973.1, data_15_18973.2]

/-- Complete interval computation for depth 15, residue 18974. -/
theorem bounds_15_18974 : exactInterval 15 18974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18974 : oddCount 18974 15 = 7 ∧ acceleratedOrbit 15 18974 = 1268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18974) = 3 ^ 7 * m + 1268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18974.1, data_15_18974.2]

/-- Complete interval computation for depth 15, residue 18975. -/
theorem bounds_15_18975 : exactInterval 15 18975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18975 : oddCount 18975 15 = 8 ∧ acceleratedOrbit 15 18975 = 3800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18975) = 3 ^ 8 * m + 3800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18975.1, data_15_18975.2]

/-- Complete interval computation for depth 15, residue 18976. -/
theorem bounds_15_18976 : exactInterval 15 18976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18976 : oddCount 18976 15 = 6 ∧ acceleratedOrbit 15 18976 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18976) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18976.1, data_15_18976.2]

/-- Complete interval computation for depth 15, residue 18977. -/
theorem bounds_15_18977 : exactInterval 15 18977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18977 : oddCount 18977 15 = 7 ∧ acceleratedOrbit 15 18977 = 1268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18977) = 3 ^ 7 * m + 1268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18977.1, data_15_18977.2]

/-- Complete interval computation for depth 15, residue 18978. -/
theorem bounds_15_18978 : exactInterval 15 18978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18978 : oddCount 18978 15 = 8 ∧ acceleratedOrbit 15 18978 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18978) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18978.1, data_15_18978.2]

/-- Complete interval computation for depth 15, residue 18979. -/
theorem bounds_15_18979 : exactInterval 15 18979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18979 : oddCount 18979 15 = 8 ∧ acceleratedOrbit 15 18979 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18979) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18979.1, data_15_18979.2]

/-- Complete interval computation for depth 15, residue 18980. -/
theorem bounds_15_18980 : exactInterval 15 18980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18980 : oddCount 18980 15 = 8 ∧ acceleratedOrbit 15 18980 = 3802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18980) = 3 ^ 8 * m + 3802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18980.1, data_15_18980.2]

/-- Complete interval computation for depth 15, residue 18981. -/
theorem bounds_15_18981 : exactInterval 15 18981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18981 : oddCount 18981 15 = 8 ∧ acceleratedOrbit 15 18981 = 3802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18981) = 3 ^ 8 * m + 3802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18981.1, data_15_18981.2]

/-- Complete interval computation for depth 15, residue 18982. -/
theorem bounds_15_18982 : exactInterval 15 18982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18982 : oddCount 18982 15 = 8 ∧ acceleratedOrbit 15 18982 = 3802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18982) = 3 ^ 8 * m + 3802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18982.1, data_15_18982.2]

/-- Complete interval computation for depth 15, residue 18983. -/
theorem bounds_15_18983 : exactInterval 15 18983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18983 : oddCount 18983 15 = 8 ∧ acceleratedOrbit 15 18983 = 3802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18983) = 3 ^ 8 * m + 3802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18983.1, data_15_18983.2]

/-- Complete interval computation for depth 15, residue 18984. -/
theorem bounds_15_18984 : exactInterval 15 18984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18984 : oddCount 18984 15 = 6 ∧ acceleratedOrbit 15 18984 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18984) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18984.1, data_15_18984.2]

/-- Complete interval computation for depth 15, residue 18985. -/
theorem bounds_15_18985 : exactInterval 15 18985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18985 : oddCount 18985 15 = 9 ∧ acceleratedOrbit 15 18985 = 11405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18985) = 3 ^ 9 * m + 11405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18985.1, data_15_18985.2]

/-- Complete interval computation for depth 15, residue 18986. -/
theorem bounds_15_18986 : exactInterval 15 18986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18986 : oddCount 18986 15 = 6 ∧ acceleratedOrbit 15 18986 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18986) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18986.1, data_15_18986.2]

/-- Complete interval computation for depth 15, residue 18987. -/
theorem bounds_15_18987 : exactInterval 15 18987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18987 : oddCount 18987 15 = 8 ∧ acceleratedOrbit 15 18987 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18987) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18987.1, data_15_18987.2]

/-- Complete interval computation for depth 15, residue 18988. -/
theorem bounds_15_18988 : exactInterval 15 18988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18988 : oddCount 18988 15 = 8 ∧ acceleratedOrbit 15 18988 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18988) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18988.1, data_15_18988.2]

/-- Complete interval computation for depth 15, residue 18989. -/
theorem bounds_15_18989 : exactInterval 15 18989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18989 : oddCount 18989 15 = 8 ∧ acceleratedOrbit 15 18989 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18989) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18989.1, data_15_18989.2]

/-- Complete interval computation for depth 15, residue 18990. -/
theorem bounds_15_18990 : exactInterval 15 18990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18990 : oddCount 18990 15 = 8 ∧ acceleratedOrbit 15 18990 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18990) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18990.1, data_15_18990.2]

/-- Complete interval computation for depth 15, residue 18991. -/
theorem bounds_15_18991 : exactInterval 15 18991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18991 : oddCount 18991 15 = 10 ∧ acceleratedOrbit 15 18991 = 34226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18991) = 3 ^ 10 * m + 34226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18991.1, data_15_18991.2]

/-- Complete interval computation for depth 15, residue 18992. -/
theorem bounds_15_18992 : exactInterval 15 18992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18992 : oddCount 18992 15 = 6 ∧ acceleratedOrbit 15 18992 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18992) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18992.1, data_15_18992.2]

/-- Complete interval computation for depth 15, residue 18993. -/
theorem bounds_15_18993 : exactInterval 15 18993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18993 : oddCount 18993 15 = 9 ∧ acceleratedOrbit 15 18993 = 11414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18993) = 3 ^ 9 * m + 11414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18993.1, data_15_18993.2]

/-- Complete interval computation for depth 15, residue 18994. -/
theorem bounds_15_18994 : exactInterval 15 18994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18994 : oddCount 18994 15 = 9 ∧ acceleratedOrbit 15 18994 = 11414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18994) = 3 ^ 9 * m + 11414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18994.1, data_15_18994.2]

/-- Complete interval computation for depth 15, residue 18995. -/
theorem bounds_15_18995 : exactInterval 15 18995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18995 : oddCount 18995 15 = 9 ∧ acceleratedOrbit 15 18995 = 11414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18995) = 3 ^ 9 * m + 11414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18995.1, data_15_18995.2]

/-- Complete interval computation for depth 15, residue 18996. -/
theorem bounds_15_18996 : exactInterval 15 18996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18996 : oddCount 18996 15 = 6 ∧ acceleratedOrbit 15 18996 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18996) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18996.1, data_15_18996.2]

/-- Complete interval computation for depth 15, residue 18997. -/
theorem bounds_15_18997 : exactInterval 15 18997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18997 : oddCount 18997 15 = 6 ∧ acceleratedOrbit 15 18997 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18997) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18997.1, data_15_18997.2]

/-- Complete interval computation for depth 15, residue 18998. -/
theorem bounds_15_18998 : exactInterval 15 18998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18998 : oddCount 18998 15 = 11 ∧ acceleratedOrbit 15 18998 = 102721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18998) = 3 ^ 11 * m + 102721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18998.1, data_15_18998.2]

/-- Complete interval computation for depth 15, residue 18999. -/
theorem bounds_15_18999 : exactInterval 15 18999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18999 : oddCount 18999 15 = 11 ∧ acceleratedOrbit 15 18999 = 102721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18999) = 3 ^ 11 * m + 102721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18999.1, data_15_18999.2]

/-- Complete interval computation for depth 15, residue 19000. -/
theorem bounds_15_19000 : exactInterval 15 19000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19000 : oddCount 19000 15 = 10 ∧ acceleratedOrbit 15 19000 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19000) = 3 ^ 10 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19000.1, data_15_19000.2]

/-- Complete interval computation for depth 15, residue 19001. -/
theorem bounds_15_19001 : exactInterval 15 19001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19001 : oddCount 19001 15 = 9 ∧ acceleratedOrbit 15 19001 = 11416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19001) = 3 ^ 9 * m + 11416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19001.1, data_15_19001.2]

/-- Complete interval computation for depth 15, residue 19002. -/
theorem bounds_15_19002 : exactInterval 15 19002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19002 : oddCount 19002 15 = 10 ∧ acceleratedOrbit 15 19002 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19002) = 3 ^ 10 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19002.1, data_15_19002.2]

/-- Complete interval computation for depth 15, residue 19003. -/
theorem bounds_15_19003 : exactInterval 15 19003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19003 : oddCount 19003 15 = 9 ∧ acceleratedOrbit 15 19003 = 11420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19003) = 3 ^ 9 * m + 11420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19003.1, data_15_19003.2]

/-- Complete interval computation for depth 15, residue 19004. -/
theorem bounds_15_19004 : exactInterval 15 19004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19004 : oddCount 19004 15 = 10 ∧ acceleratedOrbit 15 19004 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19004) = 3 ^ 10 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19004.1, data_15_19004.2]

end Collatz.Research.PassageAtlas.Batch0580
