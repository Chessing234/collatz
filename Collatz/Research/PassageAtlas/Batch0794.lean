import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0794

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25985. -/
theorem bounds_15_25985 : exactInterval 15 25985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25985 : oddCount 25985 15 = 8 ∧ acceleratedOrbit 15 25985 = 5204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25985) = 3 ^ 8 * m + 5204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25985.1, data_15_25985.2]

/-- Complete interval computation for depth 15, residue 25986. -/
theorem bounds_15_25986 : exactInterval 15 25986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25986 : oddCount 25986 15 = 5 ∧ acceleratedOrbit 15 25986 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25986) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25986.1, data_15_25986.2]

/-- Complete interval computation for depth 15, residue 25987. -/
theorem bounds_15_25987 : exactInterval 15 25987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25987 : oddCount 25987 15 = 5 ∧ acceleratedOrbit 15 25987 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25987) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25987.1, data_15_25987.2]

/-- Complete interval computation for depth 15, residue 25988. -/
theorem bounds_15_25988 : exactInterval 15 25988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25988 : oddCount 25988 15 = 8 ∧ acceleratedOrbit 15 25988 = 5206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25988) = 3 ^ 8 * m + 5206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25988.1, data_15_25988.2]

/-- Complete interval computation for depth 15, residue 25989. -/
theorem bounds_15_25989 : exactInterval 15 25989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25989 : oddCount 25989 15 = 8 ∧ acceleratedOrbit 15 25989 = 5206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25989) = 3 ^ 8 * m + 5206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25989.1, data_15_25989.2]

/-- Complete interval computation for depth 15, residue 25990. -/
theorem bounds_15_25990 : exactInterval 15 25990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25990 : oddCount 25990 15 = 8 ∧ acceleratedOrbit 15 25990 = 5206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25990) = 3 ^ 8 * m + 5206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25990.1, data_15_25990.2]

/-- Complete interval computation for depth 15, residue 25991. -/
theorem bounds_15_25991 : exactInterval 15 25991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25991 : oddCount 25991 15 = 5 ∧ acceleratedOrbit 15 25991 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25991) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25991.1, data_15_25991.2]

/-- Complete interval computation for depth 15, residue 25992. -/
theorem bounds_15_25992 : exactInterval 15 25992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25992 : oddCount 25992 15 = 6 ∧ acceleratedOrbit 15 25992 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25992) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25992.1, data_15_25992.2]

/-- Complete interval computation for depth 15, residue 25993. -/
theorem bounds_15_25993 : exactInterval 15 25993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25993 : oddCount 25993 15 = 7 ∧ acceleratedOrbit 15 25993 = 1735 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25993) = 3 ^ 7 * m + 1735 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25993.1, data_15_25993.2]

/-- Complete interval computation for depth 15, residue 25994. -/
theorem bounds_15_25994 : exactInterval 15 25994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25994 : oddCount 25994 15 = 6 ∧ acceleratedOrbit 15 25994 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25994) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25994.1, data_15_25994.2]

/-- Complete interval computation for depth 15, residue 25995. -/
theorem bounds_15_25995 : exactInterval 15 25995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25995 : oddCount 25995 15 = 8 ∧ acceleratedOrbit 15 25995 = 5206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25995) = 3 ^ 8 * m + 5206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25995.1, data_15_25995.2]

/-- Complete interval computation for depth 15, residue 25996. -/
theorem bounds_15_25996 : exactInterval 15 25996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25996 : oddCount 25996 15 = 6 ∧ acceleratedOrbit 15 25996 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25996) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25996.1, data_15_25996.2]

/-- Complete interval computation for depth 15, residue 25997. -/
theorem bounds_15_25997 : exactInterval 15 25997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25997 : oddCount 25997 15 = 6 ∧ acceleratedOrbit 15 25997 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25997) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25997.1, data_15_25997.2]

/-- Complete interval computation for depth 15, residue 25998. -/
theorem bounds_15_25998 : exactInterval 15 25998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25998 : oddCount 25998 15 = 7 ∧ acceleratedOrbit 15 25998 = 1736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25998) = 3 ^ 7 * m + 1736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25998.1, data_15_25998.2]

/-- Complete interval computation for depth 15, residue 25999. -/
theorem bounds_15_25999 : exactInterval 15 25999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25999 : oddCount 25999 15 = 7 ∧ acceleratedOrbit 15 25999 = 1736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25999) = 3 ^ 7 * m + 1736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25999.1, data_15_25999.2]

/-- Complete interval computation for depth 15, residue 26000. -/
theorem bounds_15_26000 : exactInterval 15 26000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26000 : oddCount 26000 15 = 6 ∧ acceleratedOrbit 15 26000 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26000) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26000.1, data_15_26000.2]

/-- Complete interval computation for depth 15, residue 26001. -/
theorem bounds_15_26001 : exactInterval 15 26001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26001 : oddCount 26001 15 = 8 ∧ acceleratedOrbit 15 26001 = 5210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26001) = 3 ^ 8 * m + 5210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26001.1, data_15_26001.2]

/-- Complete interval computation for depth 15, residue 26002. -/
theorem bounds_15_26002 : exactInterval 15 26002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26002 : oddCount 26002 15 = 8 ∧ acceleratedOrbit 15 26002 = 5210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26002) = 3 ^ 8 * m + 5210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26002.1, data_15_26002.2]

/-- Complete interval computation for depth 15, residue 26003. -/
theorem bounds_15_26003 : exactInterval 15 26003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26003 : oddCount 26003 15 = 8 ∧ acceleratedOrbit 15 26003 = 5210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26003) = 3 ^ 8 * m + 5210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26003.1, data_15_26003.2]

/-- Complete interval computation for depth 15, residue 26004. -/
theorem bounds_15_26004 : exactInterval 15 26004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26004 : oddCount 26004 15 = 6 ∧ acceleratedOrbit 15 26004 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26004) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26004.1, data_15_26004.2]

/-- Complete interval computation for depth 15, residue 26005. -/
theorem bounds_15_26005 : exactInterval 15 26005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26005 : oddCount 26005 15 = 6 ∧ acceleratedOrbit 15 26005 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26005) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26005.1, data_15_26005.2]

/-- Complete interval computation for depth 15, residue 26006. -/
theorem bounds_15_26006 : exactInterval 15 26006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26006 : oddCount 26006 15 = 8 ∧ acceleratedOrbit 15 26006 = 5210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26006) = 3 ^ 8 * m + 5210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26006.1, data_15_26006.2]

/-- Complete interval computation for depth 15, residue 26007. -/
theorem bounds_15_26007 : exactInterval 15 26007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26007 : oddCount 26007 15 = 8 ∧ acceleratedOrbit 15 26007 = 5210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26007) = 3 ^ 8 * m + 5210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26007.1, data_15_26007.2]

/-- Complete interval computation for depth 15, residue 26008. -/
theorem bounds_15_26008 : exactInterval 15 26008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26008 : oddCount 26008 15 = 6 ∧ acceleratedOrbit 15 26008 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26008) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26008.1, data_15_26008.2]

/-- Complete interval computation for depth 15, residue 26009. -/
theorem bounds_15_26009 : exactInterval 15 26009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26009 : oddCount 26009 15 = 8 ∧ acceleratedOrbit 15 26009 = 5210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26009) = 3 ^ 8 * m + 5210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26009.1, data_15_26009.2]

/-- Complete interval computation for depth 15, residue 26010. -/
theorem bounds_15_26010 : exactInterval 15 26010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26010 : oddCount 26010 15 = 6 ∧ acceleratedOrbit 15 26010 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26010) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26010.1, data_15_26010.2]

/-- Complete interval computation for depth 15, residue 26011. -/
theorem bounds_15_26011 : exactInterval 15 26011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26011 : oddCount 26011 15 = 9 ∧ acceleratedOrbit 15 26011 = 15626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26011) = 3 ^ 9 * m + 15626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26011.1, data_15_26011.2]

/-- Complete interval computation for depth 15, residue 26012. -/
theorem bounds_15_26012 : exactInterval 15 26012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26012 : oddCount 26012 15 = 9 ∧ acceleratedOrbit 15 26012 = 15628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26012) = 3 ^ 9 * m + 15628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26012.1, data_15_26012.2]

/-- Complete interval computation for depth 15, residue 26013. -/
theorem bounds_15_26013 : exactInterval 15 26013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26013 : oddCount 26013 15 = 9 ∧ acceleratedOrbit 15 26013 = 15628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26013) = 3 ^ 9 * m + 15628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26013.1, data_15_26013.2]

/-- Complete interval computation for depth 15, residue 26014. -/
theorem bounds_15_26014 : exactInterval 15 26014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26014 : oddCount 26014 15 = 9 ∧ acceleratedOrbit 15 26014 = 15628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26014) = 3 ^ 9 * m + 15628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26014.1, data_15_26014.2]

/-- Complete interval computation for depth 15, residue 26015. -/
theorem bounds_15_26015 : exactInterval 15 26015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26015 : oddCount 26015 15 = 10 ∧ acceleratedOrbit 15 26015 = 46882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26015) = 3 ^ 10 * m + 46882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26015.1, data_15_26015.2]

/-- Complete interval computation for depth 15, residue 26016. -/
theorem bounds_15_26016 : exactInterval 15 26016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26016 : oddCount 26016 15 = 4 ∧ acceleratedOrbit 15 26016 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26016) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26016.1, data_15_26016.2]

end Collatz.Research.PassageAtlas.Batch0794
