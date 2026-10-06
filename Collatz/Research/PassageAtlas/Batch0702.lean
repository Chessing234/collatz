import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0702

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22970. -/
theorem bounds_15_22970 : exactInterval 15 22970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22970 : oddCount 22970 15 = 7 ∧ acceleratedOrbit 15 22970 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22970) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22970.1, data_15_22970.2]

/-- Complete interval computation for depth 15, residue 22971. -/
theorem bounds_15_22971 : exactInterval 15 22971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22971 : oddCount 22971 15 = 8 ∧ acceleratedOrbit 15 22971 = 4600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22971) = 3 ^ 8 * m + 4600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22971.1, data_15_22971.2]

/-- Complete interval computation for depth 15, residue 22972. -/
theorem bounds_15_22972 : exactInterval 15 22972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22972 : oddCount 22972 15 = 8 ∧ acceleratedOrbit 15 22972 = 4601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22972) = 3 ^ 8 * m + 4601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22972.1, data_15_22972.2]

/-- Complete interval computation for depth 15, residue 22973. -/
theorem bounds_15_22973 : exactInterval 15 22973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22973 : oddCount 22973 15 = 8 ∧ acceleratedOrbit 15 22973 = 4601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22973) = 3 ^ 8 * m + 4601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22973.1, data_15_22973.2]

/-- Complete interval computation for depth 15, residue 22974. -/
theorem bounds_15_22974 : exactInterval 15 22974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22974 : oddCount 22974 15 = 8 ∧ acceleratedOrbit 15 22974 = 4601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22974) = 3 ^ 8 * m + 4601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22974.1, data_15_22974.2]

/-- Complete interval computation for depth 15, residue 22975. -/
theorem bounds_15_22975 : exactInterval 15 22975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22975 : oddCount 22975 15 = 11 ∧ acceleratedOrbit 15 22975 = 124211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22975) = 3 ^ 11 * m + 124211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22975.1, data_15_22975.2]

/-- Complete interval computation for depth 15, residue 22976. -/
theorem bounds_15_22976 : exactInterval 15 22976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22976 : oddCount 22976 15 = 8 ∧ acceleratedOrbit 15 22976 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22976) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22976.1, data_15_22976.2]

/-- Complete interval computation for depth 15, residue 22977. -/
theorem bounds_15_22977 : exactInterval 15 22977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22977 : oddCount 22977 15 = 10 ∧ acceleratedOrbit 15 22977 = 41417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22977) = 3 ^ 10 * m + 41417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22977.1, data_15_22977.2]

/-- Complete interval computation for depth 15, residue 22978. -/
theorem bounds_15_22978 : exactInterval 15 22978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22978 : oddCount 22978 15 = 10 ∧ acceleratedOrbit 15 22978 = 41417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22978) = 3 ^ 10 * m + 41417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22978.1, data_15_22978.2]

/-- Complete interval computation for depth 15, residue 22979. -/
theorem bounds_15_22979 : exactInterval 15 22979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22979 : oddCount 22979 15 = 10 ∧ acceleratedOrbit 15 22979 = 41417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22979) = 3 ^ 10 * m + 41417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22979.1, data_15_22979.2]

/-- Complete interval computation for depth 15, residue 22980. -/
theorem bounds_15_22980 : exactInterval 15 22980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22980 : oddCount 22980 15 = 3 ∧ acceleratedOrbit 15 22980 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22980) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22980.1, data_15_22980.2]

/-- Complete interval computation for depth 15, residue 22981. -/
theorem bounds_15_22981 : exactInterval 15 22981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22981 : oddCount 22981 15 = 3 ∧ acceleratedOrbit 15 22981 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22981) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22981.1, data_15_22981.2]

/-- Complete interval computation for depth 15, residue 22982. -/
theorem bounds_15_22982 : exactInterval 15 22982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22982 : oddCount 22982 15 = 3 ∧ acceleratedOrbit 15 22982 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22982) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22982.1, data_15_22982.2]

/-- Complete interval computation for depth 15, residue 22983. -/
theorem bounds_15_22983 : exactInterval 15 22983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22983 : oddCount 22983 15 = 9 ∧ acceleratedOrbit 15 22983 = 13807 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22983) = 3 ^ 9 * m + 13807 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22983.1, data_15_22983.2]

/-- Complete interval computation for depth 15, residue 22984. -/
theorem bounds_15_22984 : exactInterval 15 22984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22984 : oddCount 22984 15 = 8 ∧ acceleratedOrbit 15 22984 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22984) = 3 ^ 8 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22984.1, data_15_22984.2]

/-- Complete interval computation for depth 15, residue 22985. -/
theorem bounds_15_22985 : exactInterval 15 22985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22985 : oddCount 22985 15 = 9 ∧ acceleratedOrbit 15 22985 = 13810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22985) = 3 ^ 9 * m + 13810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22985.1, data_15_22985.2]

/-- Complete interval computation for depth 15, residue 22986. -/
theorem bounds_15_22986 : exactInterval 15 22986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22986 : oddCount 22986 15 = 8 ∧ acceleratedOrbit 15 22986 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22986) = 3 ^ 8 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22986.1, data_15_22986.2]

/-- Complete interval computation for depth 15, residue 22987. -/
theorem bounds_15_22987 : exactInterval 15 22987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22987 : oddCount 22987 15 = 6 ∧ acceleratedOrbit 15 22987 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22987) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22987.1, data_15_22987.2]

/-- Complete interval computation for depth 15, residue 22988. -/
theorem bounds_15_22988 : exactInterval 15 22988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22988 : oddCount 22988 15 = 8 ∧ acceleratedOrbit 15 22988 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22988) = 3 ^ 8 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22988.1, data_15_22988.2]

/-- Complete interval computation for depth 15, residue 22989. -/
theorem bounds_15_22989 : exactInterval 15 22989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22989 : oddCount 22989 15 = 8 ∧ acceleratedOrbit 15 22989 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22989) = 3 ^ 8 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22989.1, data_15_22989.2]

/-- Complete interval computation for depth 15, residue 22990. -/
theorem bounds_15_22990 : exactInterval 15 22990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22990 : oddCount 22990 15 = 10 ∧ acceleratedOrbit 15 22990 = 41435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22990) = 3 ^ 10 * m + 41435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22990.1, data_15_22990.2]

/-- Complete interval computation for depth 15, residue 22991. -/
theorem bounds_15_22991 : exactInterval 15 22991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22991 : oddCount 22991 15 = 10 ∧ acceleratedOrbit 15 22991 = 41435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22991) = 3 ^ 10 * m + 41435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22991.1, data_15_22991.2]

/-- Complete interval computation for depth 15, residue 22992. -/
theorem bounds_15_22992 : exactInterval 15 22992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22992 : oddCount 22992 15 = 8 ∧ acceleratedOrbit 15 22992 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22992) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22992.1, data_15_22992.2]

/-- Complete interval computation for depth 15, residue 22993. -/
theorem bounds_15_22993 : exactInterval 15 22993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22993 : oddCount 22993 15 = 8 ∧ acceleratedOrbit 15 22993 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22993) = 3 ^ 8 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22993.1, data_15_22993.2]

/-- Complete interval computation for depth 15, residue 22994. -/
theorem bounds_15_22994 : exactInterval 15 22994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22994 : oddCount 22994 15 = 7 ∧ acceleratedOrbit 15 22994 = 1535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22994) = 3 ^ 7 * m + 1535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22994.1, data_15_22994.2]

/-- Complete interval computation for depth 15, residue 22995. -/
theorem bounds_15_22995 : exactInterval 15 22995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22995 : oddCount 22995 15 = 7 ∧ acceleratedOrbit 15 22995 = 1535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22995) = 3 ^ 7 * m + 1535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22995.1, data_15_22995.2]

/-- Complete interval computation for depth 15, residue 22996. -/
theorem bounds_15_22996 : exactInterval 15 22996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22996 : oddCount 22996 15 = 8 ∧ acceleratedOrbit 15 22996 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22996) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22996.1, data_15_22996.2]

/-- Complete interval computation for depth 15, residue 22997. -/
theorem bounds_15_22997 : exactInterval 15 22997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22997 : oddCount 22997 15 = 8 ∧ acceleratedOrbit 15 22997 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22997) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22997.1, data_15_22997.2]

/-- Complete interval computation for depth 15, residue 22998. -/
theorem bounds_15_22998 : exactInterval 15 22998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22998 : oddCount 22998 15 = 9 ∧ acceleratedOrbit 15 22998 = 13817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22998) = 3 ^ 9 * m + 13817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22998.1, data_15_22998.2]

/-- Complete interval computation for depth 15, residue 22999. -/
theorem bounds_15_22999 : exactInterval 15 22999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22999 : oddCount 22999 15 = 9 ∧ acceleratedOrbit 15 22999 = 13817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22999) = 3 ^ 9 * m + 13817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22999.1, data_15_22999.2]

/-- Complete interval computation for depth 15, residue 23000. -/
theorem bounds_15_23000 : exactInterval 15 23000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23000 : oddCount 23000 15 = 7 ∧ acceleratedOrbit 15 23000 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23000) = 3 ^ 7 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23000.1, data_15_23000.2]

/-- Complete interval computation for depth 15, residue 23001. -/
theorem bounds_15_23001 : exactInterval 15 23001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23001 : oddCount 23001 15 = 7 ∧ acceleratedOrbit 15 23001 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23001) = 3 ^ 7 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23001.1, data_15_23001.2]

/-- Complete interval computation for depth 15, residue 23002. -/
theorem bounds_15_23002 : exactInterval 15 23002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23002 : oddCount 23002 15 = 7 ∧ acceleratedOrbit 15 23002 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23002) = 3 ^ 7 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23002.1, data_15_23002.2]

end Collatz.Research.PassageAtlas.Batch0702
