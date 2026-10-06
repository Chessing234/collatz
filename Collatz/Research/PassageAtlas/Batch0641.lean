import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0641

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20971. -/
theorem bounds_15_20971 : exactInterval 15 20971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20971 : oddCount 20971 15 = 9 ∧ acceleratedOrbit 15 20971 = 12598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20971) = 3 ^ 9 * m + 12598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20971.1, data_15_20971.2]

/-- Complete interval computation for depth 15, residue 20972. -/
theorem bounds_15_20972 : exactInterval 15 20972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20972 : oddCount 20972 15 = 8 ∧ acceleratedOrbit 15 20972 = 4202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20972) = 3 ^ 8 * m + 4202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20972.1, data_15_20972.2]

/-- Complete interval computation for depth 15, residue 20973. -/
theorem bounds_15_20973 : exactInterval 15 20973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20973 : oddCount 20973 15 = 8 ∧ acceleratedOrbit 15 20973 = 4202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20973) = 3 ^ 8 * m + 4202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20973.1, data_15_20973.2]

/-- Complete interval computation for depth 15, residue 20974. -/
theorem bounds_15_20974 : exactInterval 15 20974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20974 : oddCount 20974 15 = 8 ∧ acceleratedOrbit 15 20974 = 4202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20974) = 3 ^ 8 * m + 4202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20974.1, data_15_20974.2]

/-- Complete interval computation for depth 15, residue 20975. -/
theorem bounds_15_20975 : exactInterval 15 20975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20975 : oddCount 20975 15 = 13 ∧ acceleratedOrbit 15 20975 = 1020599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20975) = 3 ^ 13 * m + 1020599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20975.1, data_15_20975.2]

/-- Complete interval computation for depth 15, residue 20976. -/
theorem bounds_15_20976 : exactInterval 15 20976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20976 : oddCount 20976 15 = 6 ∧ acceleratedOrbit 15 20976 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20976) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20976.1, data_15_20976.2]

/-- Complete interval computation for depth 15, residue 20977. -/
theorem bounds_15_20977 : exactInterval 15 20977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20977 : oddCount 20977 15 = 7 ∧ acceleratedOrbit 15 20977 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20977) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20977.1, data_15_20977.2]

/-- Complete interval computation for depth 15, residue 20978. -/
theorem bounds_15_20978 : exactInterval 15 20978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20978 : oddCount 20978 15 = 8 ∧ acceleratedOrbit 15 20978 = 4202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20978) = 3 ^ 8 * m + 4202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20978.1, data_15_20978.2]

/-- Complete interval computation for depth 15, residue 20979. -/
theorem bounds_15_20979 : exactInterval 15 20979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20979 : oddCount 20979 15 = 8 ∧ acceleratedOrbit 15 20979 = 4202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20979) = 3 ^ 8 * m + 4202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20979.1, data_15_20979.2]

/-- Complete interval computation for depth 15, residue 20980. -/
theorem bounds_15_20980 : exactInterval 15 20980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20980 : oddCount 20980 15 = 6 ∧ acceleratedOrbit 15 20980 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20980) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20980.1, data_15_20980.2]

/-- Complete interval computation for depth 15, residue 20981. -/
theorem bounds_15_20981 : exactInterval 15 20981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20981 : oddCount 20981 15 = 6 ∧ acceleratedOrbit 15 20981 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20981) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20981.1, data_15_20981.2]

/-- Complete interval computation for depth 15, residue 20982. -/
theorem bounds_15_20982 : exactInterval 15 20982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20982 : oddCount 20982 15 = 10 ∧ acceleratedOrbit 15 20982 = 37817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20982) = 3 ^ 10 * m + 37817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20982.1, data_15_20982.2]

/-- Complete interval computation for depth 15, residue 20983. -/
theorem bounds_15_20983 : exactInterval 15 20983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20983 : oddCount 20983 15 = 10 ∧ acceleratedOrbit 15 20983 = 37817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20983) = 3 ^ 10 * m + 37817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20983.1, data_15_20983.2]

/-- Complete interval computation for depth 15, residue 20984. -/
theorem bounds_15_20984 : exactInterval 15 20984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20984 : oddCount 20984 15 = 6 ∧ acceleratedOrbit 15 20984 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20984) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20984.1, data_15_20984.2]

/-- Complete interval computation for depth 15, residue 20985. -/
theorem bounds_15_20985 : exactInterval 15 20985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20985 : oddCount 20985 15 = 9 ∧ acceleratedOrbit 15 20985 = 12608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20985) = 3 ^ 9 * m + 12608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20985.1, data_15_20985.2]

/-- Complete interval computation for depth 15, residue 20986. -/
theorem bounds_15_20986 : exactInterval 15 20986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20986 : oddCount 20986 15 = 6 ∧ acceleratedOrbit 15 20986 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20986) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20986.1, data_15_20986.2]

/-- Complete interval computation for depth 15, residue 20987. -/
theorem bounds_15_20987 : exactInterval 15 20987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20987 : oddCount 20987 15 = 10 ∧ acceleratedOrbit 15 20987 = 37826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20987) = 3 ^ 10 * m + 37826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20987.1, data_15_20987.2]

/-- Complete interval computation for depth 15, residue 20988. -/
theorem bounds_15_20988 : exactInterval 15 20988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20988 : oddCount 20988 15 = 10 ∧ acceleratedOrbit 15 20988 = 37829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20988) = 3 ^ 10 * m + 37829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20988.1, data_15_20988.2]

/-- Complete interval computation for depth 15, residue 20989. -/
theorem bounds_15_20989 : exactInterval 15 20989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20989 : oddCount 20989 15 = 10 ∧ acceleratedOrbit 15 20989 = 37829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20989) = 3 ^ 10 * m + 37829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20989.1, data_15_20989.2]

/-- Complete interval computation for depth 15, residue 20990. -/
theorem bounds_15_20990 : exactInterval 15 20990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20990 : oddCount 20990 15 = 10 ∧ acceleratedOrbit 15 20990 = 37829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20990) = 3 ^ 10 * m + 37829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20990.1, data_15_20990.2]

/-- Complete interval computation for depth 15, residue 20991. -/
theorem bounds_15_20991 : exactInterval 15 20991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20991 : oddCount 20991 15 = 11 ∧ acceleratedOrbit 15 20991 = 113485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20991) = 3 ^ 11 * m + 113485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20991.1, data_15_20991.2]

/-- Complete interval computation for depth 15, residue 20992. -/
theorem bounds_15_20992 : exactInterval 15 20992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20992 : oddCount 20992 15 = 5 ∧ acceleratedOrbit 15 20992 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20992) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20992.1, data_15_20992.2]

/-- Complete interval computation for depth 15, residue 20993. -/
theorem bounds_15_20993 : exactInterval 15 20993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20993 : oddCount 20993 15 = 8 ∧ acceleratedOrbit 15 20993 = 4205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20993) = 3 ^ 8 * m + 4205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20993.1, data_15_20993.2]

/-- Complete interval computation for depth 15, residue 20994. -/
theorem bounds_15_20994 : exactInterval 15 20994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20994 : oddCount 20994 15 = 7 ∧ acceleratedOrbit 15 20994 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20994) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20994.1, data_15_20994.2]

/-- Complete interval computation for depth 15, residue 20995. -/
theorem bounds_15_20995 : exactInterval 15 20995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20995 : oddCount 20995 15 = 7 ∧ acceleratedOrbit 15 20995 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20995) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20995.1, data_15_20995.2]

/-- Complete interval computation for depth 15, residue 20996. -/
theorem bounds_15_20996 : exactInterval 15 20996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20996 : oddCount 20996 15 = 8 ∧ acceleratedOrbit 15 20996 = 4207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20996) = 3 ^ 8 * m + 4207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20996.1, data_15_20996.2]

/-- Complete interval computation for depth 15, residue 20997. -/
theorem bounds_15_20997 : exactInterval 15 20997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20997 : oddCount 20997 15 = 8 ∧ acceleratedOrbit 15 20997 = 4207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20997) = 3 ^ 8 * m + 4207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20997.1, data_15_20997.2]

/-- Complete interval computation for depth 15, residue 20998. -/
theorem bounds_15_20998 : exactInterval 15 20998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20998 : oddCount 20998 15 = 8 ∧ acceleratedOrbit 15 20998 = 4207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20998) = 3 ^ 8 * m + 4207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20998.1, data_15_20998.2]

/-- Complete interval computation for depth 15, residue 20999. -/
theorem bounds_15_20999 : exactInterval 15 20999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20999 : oddCount 20999 15 = 10 ∧ acceleratedOrbit 15 20999 = 37847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20999) = 3 ^ 10 * m + 37847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20999.1, data_15_20999.2]

/-- Complete interval computation for depth 15, residue 21000. -/
theorem bounds_15_21000 : exactInterval 15 21000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21000 : oddCount 21000 15 = 4 ∧ acceleratedOrbit 15 21000 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21000) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21000.1, data_15_21000.2]

/-- Complete interval computation for depth 15, residue 21001. -/
theorem bounds_15_21001 : exactInterval 15 21001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21001 : oddCount 21001 15 = 7 ∧ acceleratedOrbit 15 21001 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21001) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21001.1, data_15_21001.2]

/-- Complete interval computation for depth 15, residue 21002. -/
theorem bounds_15_21002 : exactInterval 15 21002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21002 : oddCount 21002 15 = 4 ∧ acceleratedOrbit 15 21002 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21002) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21002.1, data_15_21002.2]

/-- Complete interval computation for depth 15, residue 21003. -/
theorem bounds_15_21003 : exactInterval 15 21003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21003 : oddCount 21003 15 = 8 ∧ acceleratedOrbit 15 21003 = 4207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21003) = 3 ^ 8 * m + 4207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21003.1, data_15_21003.2]

end Collatz.Research.PassageAtlas.Batch0641
