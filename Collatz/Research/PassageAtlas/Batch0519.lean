import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0519

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16973. -/
theorem bounds_15_16973 : exactInterval 15 16973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16973 : oddCount 16973 15 = 9 ∧ acceleratedOrbit 15 16973 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16973) = 3 ^ 9 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16973.1, data_15_16973.2]

/-- Complete interval computation for depth 15, residue 16974. -/
theorem bounds_15_16974 : exactInterval 15 16974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16974 : oddCount 16974 15 = 9 ∧ acceleratedOrbit 15 16974 = 10199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16974) = 3 ^ 9 * m + 10199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16974.1, data_15_16974.2]

/-- Complete interval computation for depth 15, residue 16975. -/
theorem bounds_15_16975 : exactInterval 15 16975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16975 : oddCount 16975 15 = 9 ∧ acceleratedOrbit 15 16975 = 10199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16975) = 3 ^ 9 * m + 10199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16975.1, data_15_16975.2]

/-- Complete interval computation for depth 15, residue 16976. -/
theorem bounds_15_16976 : exactInterval 15 16976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16976 : oddCount 16976 15 = 6 ∧ acceleratedOrbit 15 16976 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16976) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16976.1, data_15_16976.2]

/-- Complete interval computation for depth 15, residue 16977. -/
theorem bounds_15_16977 : exactInterval 15 16977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16977 : oddCount 16977 15 = 9 ∧ acceleratedOrbit 15 16977 = 10201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16977) = 3 ^ 9 * m + 10201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16977.1, data_15_16977.2]

/-- Complete interval computation for depth 15, residue 16978. -/
theorem bounds_15_16978 : exactInterval 15 16978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16978 : oddCount 16978 15 = 9 ∧ acceleratedOrbit 15 16978 = 10201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16978) = 3 ^ 9 * m + 10201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16978.1, data_15_16978.2]

/-- Complete interval computation for depth 15, residue 16979. -/
theorem bounds_15_16979 : exactInterval 15 16979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16979 : oddCount 16979 15 = 9 ∧ acceleratedOrbit 15 16979 = 10201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16979) = 3 ^ 9 * m + 10201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16979.1, data_15_16979.2]

/-- Complete interval computation for depth 15, residue 16980. -/
theorem bounds_15_16980 : exactInterval 15 16980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16980 : oddCount 16980 15 = 6 ∧ acceleratedOrbit 15 16980 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16980) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16980.1, data_15_16980.2]

/-- Complete interval computation for depth 15, residue 16981. -/
theorem bounds_15_16981 : exactInterval 15 16981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16981 : oddCount 16981 15 = 6 ∧ acceleratedOrbit 15 16981 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16981) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16981.1, data_15_16981.2]

/-- Complete interval computation for depth 15, residue 16982. -/
theorem bounds_15_16982 : exactInterval 15 16982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16982 : oddCount 16982 15 = 10 ∧ acceleratedOrbit 15 16982 = 30617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16982) = 3 ^ 10 * m + 30617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16982.1, data_15_16982.2]

/-- Complete interval computation for depth 15, residue 16983. -/
theorem bounds_15_16983 : exactInterval 15 16983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16983 : oddCount 16983 15 = 10 ∧ acceleratedOrbit 15 16983 = 30617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16983) = 3 ^ 10 * m + 30617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16983.1, data_15_16983.2]

/-- Complete interval computation for depth 15, residue 16984. -/
theorem bounds_15_16984 : exactInterval 15 16984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16984 : oddCount 16984 15 = 3 ∧ acceleratedOrbit 15 16984 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16984) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16984.1, data_15_16984.2]

/-- Complete interval computation for depth 15, residue 16985. -/
theorem bounds_15_16985 : exactInterval 15 16985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16985 : oddCount 16985 15 = 11 ∧ acceleratedOrbit 15 16985 = 91853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16985) = 3 ^ 11 * m + 91853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16985.1, data_15_16985.2]

/-- Complete interval computation for depth 15, residue 16986. -/
theorem bounds_15_16986 : exactInterval 15 16986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16986 : oddCount 16986 15 = 3 ∧ acceleratedOrbit 15 16986 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16986) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16986.1, data_15_16986.2]

/-- Complete interval computation for depth 15, residue 16987. -/
theorem bounds_15_16987 : exactInterval 15 16987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16987 : oddCount 16987 15 = 11 ∧ acceleratedOrbit 15 16987 = 91844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16987) = 3 ^ 11 * m + 91844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16987.1, data_15_16987.2]

/-- Complete interval computation for depth 15, residue 16988. -/
theorem bounds_15_16988 : exactInterval 15 16988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16988 : oddCount 16988 15 = 3 ∧ acceleratedOrbit 15 16988 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16988) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16988.1, data_15_16988.2]

/-- Complete interval computation for depth 15, residue 16989. -/
theorem bounds_15_16989 : exactInterval 15 16989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16989 : oddCount 16989 15 = 3 ∧ acceleratedOrbit 15 16989 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16989) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16989.1, data_15_16989.2]

/-- Complete interval computation for depth 15, residue 16990. -/
theorem bounds_15_16990 : exactInterval 15 16990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16990 : oddCount 16990 15 = 9 ∧ acceleratedOrbit 15 16990 = 10208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16990) = 3 ^ 9 * m + 10208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16990.1, data_15_16990.2]

/-- Complete interval computation for depth 15, residue 16991. -/
theorem bounds_15_16991 : exactInterval 15 16991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16991 : oddCount 16991 15 = 9 ∧ acceleratedOrbit 15 16991 = 10208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16991) = 3 ^ 9 * m + 10208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16991.1, data_15_16991.2]

/-- Complete interval computation for depth 15, residue 16992. -/
theorem bounds_15_16992 : exactInterval 15 16992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16992 : oddCount 16992 15 = 6 ∧ acceleratedOrbit 15 16992 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16992) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16992.1, data_15_16992.2]

/-- Complete interval computation for depth 15, residue 16993. -/
theorem bounds_15_16993 : exactInterval 15 16993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16993 : oddCount 16993 15 = 8 ∧ acceleratedOrbit 15 16993 = 3404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16993) = 3 ^ 8 * m + 3404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16993.1, data_15_16993.2]

/-- Complete interval computation for depth 15, residue 16994. -/
theorem bounds_15_16994 : exactInterval 15 16994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16994 : oddCount 16994 15 = 7 ∧ acceleratedOrbit 15 16994 = 1136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16994) = 3 ^ 7 * m + 1136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16994.1, data_15_16994.2]

/-- Complete interval computation for depth 15, residue 16995. -/
theorem bounds_15_16995 : exactInterval 15 16995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16995 : oddCount 16995 15 = 7 ∧ acceleratedOrbit 15 16995 = 1136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16995) = 3 ^ 7 * m + 1136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16995.1, data_15_16995.2]

/-- Complete interval computation for depth 15, residue 16996. -/
theorem bounds_15_16996 : exactInterval 15 16996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16996 : oddCount 16996 15 = 7 ∧ acceleratedOrbit 15 16996 = 1136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16996) = 3 ^ 7 * m + 1136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16996.1, data_15_16996.2]

/-- Complete interval computation for depth 15, residue 16997. -/
theorem bounds_15_16997 : exactInterval 15 16997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16997 : oddCount 16997 15 = 7 ∧ acceleratedOrbit 15 16997 = 1136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16997) = 3 ^ 7 * m + 1136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16997.1, data_15_16997.2]

/-- Complete interval computation for depth 15, residue 16998. -/
theorem bounds_15_16998 : exactInterval 15 16998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16998 : oddCount 16998 15 = 7 ∧ acceleratedOrbit 15 16998 = 1136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16998) = 3 ^ 7 * m + 1136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16998.1, data_15_16998.2]

/-- Complete interval computation for depth 15, residue 16999. -/
theorem bounds_15_16999 : exactInterval 15 16999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16999 : oddCount 16999 15 = 8 ∧ acceleratedOrbit 15 16999 = 3404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16999) = 3 ^ 8 * m + 3404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16999.1, data_15_16999.2]

/-- Complete interval computation for depth 15, residue 17000. -/
theorem bounds_15_17000 : exactInterval 15 17000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17000 : oddCount 17000 15 = 6 ∧ acceleratedOrbit 15 17000 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17000) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17000.1, data_15_17000.2]

/-- Complete interval computation for depth 15, residue 17001. -/
theorem bounds_15_17001 : exactInterval 15 17001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17001 : oddCount 17001 15 = 9 ∧ acceleratedOrbit 15 17001 = 10214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17001) = 3 ^ 9 * m + 10214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17001.1, data_15_17001.2]

/-- Complete interval computation for depth 15, residue 17002. -/
theorem bounds_15_17002 : exactInterval 15 17002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17002 : oddCount 17002 15 = 6 ∧ acceleratedOrbit 15 17002 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17002) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17002.1, data_15_17002.2]

/-- Complete interval computation for depth 15, residue 17003. -/
theorem bounds_15_17003 : exactInterval 15 17003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17003 : oddCount 17003 15 = 7 ∧ acceleratedOrbit 15 17003 = 1135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17003) = 3 ^ 7 * m + 1135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17003.1, data_15_17003.2]

/-- Complete interval computation for depth 15, residue 17004. -/
theorem bounds_15_17004 : exactInterval 15 17004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17004 : oddCount 17004 15 = 8 ∧ acceleratedOrbit 15 17004 = 3406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17004) = 3 ^ 8 * m + 3406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17004.1, data_15_17004.2]

/-- Complete interval computation for depth 15, residue 17005. -/
theorem bounds_15_17005 : exactInterval 15 17005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17005 : oddCount 17005 15 = 8 ∧ acceleratedOrbit 15 17005 = 3406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17005) = 3 ^ 8 * m + 3406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17005.1, data_15_17005.2]

end Collatz.Research.PassageAtlas.Batch0519
