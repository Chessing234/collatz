import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0977

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31981. -/
theorem bounds_15_31981 : exactInterval 15 31981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31981 : oddCount 31981 15 = 6 ∧ acceleratedOrbit 15 31981 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31981) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31981.1, data_15_31981.2]

/-- Complete interval computation for depth 15, residue 31982. -/
theorem bounds_15_31982 : exactInterval 15 31982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31982 : oddCount 31982 15 = 6 ∧ acceleratedOrbit 15 31982 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31982) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31982.1, data_15_31982.2]

/-- Complete interval computation for depth 15, residue 31983. -/
theorem bounds_15_31983 : exactInterval 15 31983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31983 : oddCount 31983 15 = 11 ∧ acceleratedOrbit 15 31983 = 172910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31983) = 3 ^ 11 * m + 172910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31983.1, data_15_31983.2]

/-- Complete interval computation for depth 15, residue 31984. -/
theorem bounds_15_31984 : exactInterval 15 31984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31984 : oddCount 31984 15 = 6 ∧ acceleratedOrbit 15 31984 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31984) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31984.1, data_15_31984.2]

/-- Complete interval computation for depth 15, residue 31985. -/
theorem bounds_15_31985 : exactInterval 15 31985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31985 : oddCount 31985 15 = 6 ∧ acceleratedOrbit 15 31985 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31985) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31985.1, data_15_31985.2]

/-- Complete interval computation for depth 15, residue 31986. -/
theorem bounds_15_31986 : exactInterval 15 31986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31986 : oddCount 31986 15 = 9 ∧ acceleratedOrbit 15 31986 = 19217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31986) = 3 ^ 9 * m + 19217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31986.1, data_15_31986.2]

/-- Complete interval computation for depth 15, residue 31987. -/
theorem bounds_15_31987 : exactInterval 15 31987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31987 : oddCount 31987 15 = 9 ∧ acceleratedOrbit 15 31987 = 19217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31987) = 3 ^ 9 * m + 19217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31987.1, data_15_31987.2]

/-- Complete interval computation for depth 15, residue 31988. -/
theorem bounds_15_31988 : exactInterval 15 31988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31988 : oddCount 31988 15 = 6 ∧ acceleratedOrbit 15 31988 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31988) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31988.1, data_15_31988.2]

/-- Complete interval computation for depth 15, residue 31989. -/
theorem bounds_15_31989 : exactInterval 15 31989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31989 : oddCount 31989 15 = 6 ∧ acceleratedOrbit 15 31989 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31989) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31989.1, data_15_31989.2]

/-- Complete interval computation for depth 15, residue 31990. -/
theorem bounds_15_31990 : exactInterval 15 31990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31990 : oddCount 31990 15 = 6 ∧ acceleratedOrbit 15 31990 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31990) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31990.1, data_15_31990.2]

/-- Complete interval computation for depth 15, residue 31991. -/
theorem bounds_15_31991 : exactInterval 15 31991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31991 : oddCount 31991 15 = 6 ∧ acceleratedOrbit 15 31991 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31991) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31991.1, data_15_31991.2]

/-- Complete interval computation for depth 15, residue 31992. -/
theorem bounds_15_31992 : exactInterval 15 31992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31992 : oddCount 31992 15 = 9 ∧ acceleratedOrbit 15 31992 = 19223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31992) = 3 ^ 9 * m + 19223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31992.1, data_15_31992.2]

/-- Complete interval computation for depth 15, residue 31993. -/
theorem bounds_15_31993 : exactInterval 15 31993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31993 : oddCount 31993 15 = 8 ∧ acceleratedOrbit 15 31993 = 6407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31993) = 3 ^ 8 * m + 6407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31993.1, data_15_31993.2]

/-- Complete interval computation for depth 15, residue 31994. -/
theorem bounds_15_31994 : exactInterval 15 31994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31994 : oddCount 31994 15 = 9 ∧ acceleratedOrbit 15 31994 = 19223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31994) = 3 ^ 9 * m + 19223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31994.1, data_15_31994.2]

/-- Complete interval computation for depth 15, residue 31995. -/
theorem bounds_15_31995 : exactInterval 15 31995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31995 : oddCount 31995 15 = 11 ∧ acceleratedOrbit 15 31995 = 172979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31995) = 3 ^ 11 * m + 172979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31995.1, data_15_31995.2]

/-- Complete interval computation for depth 15, residue 31996. -/
theorem bounds_15_31996 : exactInterval 15 31996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31996 : oddCount 31996 15 = 9 ∧ acceleratedOrbit 15 31996 = 19223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31996) = 3 ^ 9 * m + 19223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31996.1, data_15_31996.2]

/-- Complete interval computation for depth 15, residue 31997. -/
theorem bounds_15_31997 : exactInterval 15 31997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31997 : oddCount 31997 15 = 9 ∧ acceleratedOrbit 15 31997 = 19223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31997) = 3 ^ 9 * m + 19223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31997.1, data_15_31997.2]

/-- Complete interval computation for depth 15, residue 31998. -/
theorem bounds_15_31998 : exactInterval 15 31998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31998 : oddCount 31998 15 = 12 ∧ acceleratedOrbit 15 31998 = 518987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31998) = 3 ^ 12 * m + 518987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31998.1, data_15_31998.2]

/-- Complete interval computation for depth 15, residue 31999. -/
theorem bounds_15_31999 : exactInterval 15 31999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31999 : oddCount 31999 15 = 12 ∧ acceleratedOrbit 15 31999 = 518987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31999) = 3 ^ 12 * m + 518987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31999.1, data_15_31999.2]

/-- Complete interval computation for depth 15, residue 32000. -/
theorem bounds_15_32000 : exactInterval 15 32000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32000 : oddCount 32000 15 = 5 ∧ acceleratedOrbit 15 32000 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32000) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32000.1, data_15_32000.2]

/-- Complete interval computation for depth 15, residue 32001. -/
theorem bounds_15_32001 : exactInterval 15 32001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32001 : oddCount 32001 15 = 8 ∧ acceleratedOrbit 15 32001 = 6409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32001) = 3 ^ 8 * m + 6409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32001.1, data_15_32001.2]

/-- Complete interval computation for depth 15, residue 32002. -/
theorem bounds_15_32002 : exactInterval 15 32002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32002 : oddCount 32002 15 = 8 ∧ acceleratedOrbit 15 32002 = 6409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32002) = 3 ^ 8 * m + 6409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32002.1, data_15_32002.2]

/-- Complete interval computation for depth 15, residue 32003. -/
theorem bounds_15_32003 : exactInterval 15 32003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32003 : oddCount 32003 15 = 8 ∧ acceleratedOrbit 15 32003 = 6409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32003) = 3 ^ 8 * m + 6409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32003.1, data_15_32003.2]

/-- Complete interval computation for depth 15, residue 32004. -/
theorem bounds_15_32004 : exactInterval 15 32004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32004 : oddCount 32004 15 = 5 ∧ acceleratedOrbit 15 32004 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32004) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32004.1, data_15_32004.2]

/-- Complete interval computation for depth 15, residue 32005. -/
theorem bounds_15_32005 : exactInterval 15 32005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32005 : oddCount 32005 15 = 5 ∧ acceleratedOrbit 15 32005 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32005) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32005.1, data_15_32005.2]

/-- Complete interval computation for depth 15, residue 32006. -/
theorem bounds_15_32006 : exactInterval 15 32006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32006 : oddCount 32006 15 = 5 ∧ acceleratedOrbit 15 32006 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32006) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32006.1, data_15_32006.2]

/-- Complete interval computation for depth 15, residue 32007. -/
theorem bounds_15_32007 : exactInterval 15 32007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32007 : oddCount 32007 15 = 10 ∧ acceleratedOrbit 15 32007 = 57682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32007) = 3 ^ 10 * m + 57682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32007.1, data_15_32007.2]

/-- Complete interval computation for depth 15, residue 32008. -/
theorem bounds_15_32008 : exactInterval 15 32008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32008 : oddCount 32008 15 = 6 ∧ acceleratedOrbit 15 32008 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32008) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32008.1, data_15_32008.2]

/-- Complete interval computation for depth 15, residue 32009. -/
theorem bounds_15_32009 : exactInterval 15 32009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32009 : oddCount 32009 15 = 8 ∧ acceleratedOrbit 15 32009 = 6410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32009) = 3 ^ 8 * m + 6410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32009.1, data_15_32009.2]

/-- Complete interval computation for depth 15, residue 32010. -/
theorem bounds_15_32010 : exactInterval 15 32010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32010 : oddCount 32010 15 = 6 ∧ acceleratedOrbit 15 32010 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32010) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32010.1, data_15_32010.2]

/-- Complete interval computation for depth 15, residue 32011. -/
theorem bounds_15_32011 : exactInterval 15 32011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32011 : oddCount 32011 15 = 7 ∧ acceleratedOrbit 15 32011 = 2137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32011) = 3 ^ 7 * m + 2137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32011.1, data_15_32011.2]

/-- Complete interval computation for depth 15, residue 32012. -/
theorem bounds_15_32012 : exactInterval 15 32012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32012 : oddCount 32012 15 = 6 ∧ acceleratedOrbit 15 32012 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32012) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32012.1, data_15_32012.2]

/-- Complete interval computation for depth 15, residue 32013. -/
theorem bounds_15_32013 : exactInterval 15 32013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32013 : oddCount 32013 15 = 6 ∧ acceleratedOrbit 15 32013 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32013) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32013.1, data_15_32013.2]

end Collatz.Research.PassageAtlas.Batch0977
