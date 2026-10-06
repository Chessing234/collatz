import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0916

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29982. -/
theorem bounds_15_29982 : exactInterval 15 29982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29982 : oddCount 29982 15 = 8 ∧ acceleratedOrbit 15 29982 = 6004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29982) = 3 ^ 8 * m + 6004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29982.1, data_15_29982.2]

/-- Complete interval computation for depth 15, residue 29983. -/
theorem bounds_15_29983 : exactInterval 15 29983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29983 : oddCount 29983 15 = 8 ∧ acceleratedOrbit 15 29983 = 6004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29983) = 3 ^ 8 * m + 6004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29983.1, data_15_29983.2]

/-- Complete interval computation for depth 15, residue 29984. -/
theorem bounds_15_29984 : exactInterval 15 29984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29984 : oddCount 29984 15 = 8 ∧ acceleratedOrbit 15 29984 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29984) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29984.1, data_15_29984.2]

/-- Complete interval computation for depth 15, residue 29985. -/
theorem bounds_15_29985 : exactInterval 15 29985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29985 : oddCount 29985 15 = 6 ∧ acceleratedOrbit 15 29985 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29985) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29985.1, data_15_29985.2]

/-- Complete interval computation for depth 15, residue 29986. -/
theorem bounds_15_29986 : exactInterval 15 29986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29986 : oddCount 29986 15 = 8 ∧ acceleratedOrbit 15 29986 = 6007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29986) = 3 ^ 8 * m + 6007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29986.1, data_15_29986.2]

/-- Complete interval computation for depth 15, residue 29987. -/
theorem bounds_15_29987 : exactInterval 15 29987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29987 : oddCount 29987 15 = 8 ∧ acceleratedOrbit 15 29987 = 6007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29987) = 3 ^ 8 * m + 6007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29987.1, data_15_29987.2]

/-- Complete interval computation for depth 15, residue 29988. -/
theorem bounds_15_29988 : exactInterval 15 29988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29988 : oddCount 29988 15 = 8 ∧ acceleratedOrbit 15 29988 = 6007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29988) = 3 ^ 8 * m + 6007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29988.1, data_15_29988.2]

/-- Complete interval computation for depth 15, residue 29989. -/
theorem bounds_15_29989 : exactInterval 15 29989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29989 : oddCount 29989 15 = 8 ∧ acceleratedOrbit 15 29989 = 6007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29989) = 3 ^ 8 * m + 6007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29989.1, data_15_29989.2]

/-- Complete interval computation for depth 15, residue 29990. -/
theorem bounds_15_29990 : exactInterval 15 29990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29990 : oddCount 29990 15 = 8 ∧ acceleratedOrbit 15 29990 = 6007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29990) = 3 ^ 8 * m + 6007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29990.1, data_15_29990.2]

/-- Complete interval computation for depth 15, residue 29991. -/
theorem bounds_15_29991 : exactInterval 15 29991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29991 : oddCount 29991 15 = 7 ∧ acceleratedOrbit 15 29991 = 2002 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29991) = 3 ^ 7 * m + 2002 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29991.1, data_15_29991.2]

/-- Complete interval computation for depth 15, residue 29992. -/
theorem bounds_15_29992 : exactInterval 15 29992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29992 : oddCount 29992 15 = 8 ∧ acceleratedOrbit 15 29992 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29992) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29992.1, data_15_29992.2]

/-- Complete interval computation for depth 15, residue 29993. -/
theorem bounds_15_29993 : exactInterval 15 29993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29993 : oddCount 29993 15 = 10 ∧ acceleratedOrbit 15 29993 = 54053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29993) = 3 ^ 10 * m + 54053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29993.1, data_15_29993.2]

/-- Complete interval computation for depth 15, residue 29994. -/
theorem bounds_15_29994 : exactInterval 15 29994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29994 : oddCount 29994 15 = 8 ∧ acceleratedOrbit 15 29994 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29994) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29994.1, data_15_29994.2]

/-- Complete interval computation for depth 15, residue 29995. -/
theorem bounds_15_29995 : exactInterval 15 29995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29995 : oddCount 29995 15 = 8 ∧ acceleratedOrbit 15 29995 = 6007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29995) = 3 ^ 8 * m + 6007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29995.1, data_15_29995.2]

/-- Complete interval computation for depth 15, residue 29996. -/
theorem bounds_15_29996 : exactInterval 15 29996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29996 : oddCount 29996 15 = 6 ∧ acceleratedOrbit 15 29996 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29996) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29996.1, data_15_29996.2]

/-- Complete interval computation for depth 15, residue 29997. -/
theorem bounds_15_29997 : exactInterval 15 29997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29997 : oddCount 29997 15 = 6 ∧ acceleratedOrbit 15 29997 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29997) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29997.1, data_15_29997.2]

/-- Complete interval computation for depth 15, residue 29998. -/
theorem bounds_15_29998 : exactInterval 15 29998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29998 : oddCount 29998 15 = 6 ∧ acceleratedOrbit 15 29998 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29998) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29998.1, data_15_29998.2]

/-- Complete interval computation for depth 15, residue 29999. -/
theorem bounds_15_29999 : exactInterval 15 29999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29999 : oddCount 29999 15 = 11 ∧ acceleratedOrbit 15 29999 = 162188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29999) = 3 ^ 11 * m + 162188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29999.1, data_15_29999.2]

/-- Complete interval computation for depth 15, residue 30000. -/
theorem bounds_15_30000 : exactInterval 15 30000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30000 : oddCount 30000 15 = 8 ∧ acceleratedOrbit 15 30000 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30000) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30000.1, data_15_30000.2]

/-- Complete interval computation for depth 15, residue 30001. -/
theorem bounds_15_30001 : exactInterval 15 30001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30001 : oddCount 30001 15 = 7 ∧ acceleratedOrbit 15 30001 = 2003 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30001) = 3 ^ 7 * m + 2003 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30001.1, data_15_30001.2]

/-- Complete interval computation for depth 15, residue 30002. -/
theorem bounds_15_30002 : exactInterval 15 30002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30002 : oddCount 30002 15 = 7 ∧ acceleratedOrbit 15 30002 = 2003 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30002) = 3 ^ 7 * m + 2003 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30002.1, data_15_30002.2]

/-- Complete interval computation for depth 15, residue 30003. -/
theorem bounds_15_30003 : exactInterval 15 30003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30003 : oddCount 30003 15 = 7 ∧ acceleratedOrbit 15 30003 = 2003 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30003) = 3 ^ 7 * m + 2003 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30003.1, data_15_30003.2]

/-- Complete interval computation for depth 15, residue 30004. -/
theorem bounds_15_30004 : exactInterval 15 30004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30004 : oddCount 30004 15 = 8 ∧ acceleratedOrbit 15 30004 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30004) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30004.1, data_15_30004.2]

/-- Complete interval computation for depth 15, residue 30005. -/
theorem bounds_15_30005 : exactInterval 15 30005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30005 : oddCount 30005 15 = 8 ∧ acceleratedOrbit 15 30005 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30005) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30005.1, data_15_30005.2]

/-- Complete interval computation for depth 15, residue 30006. -/
theorem bounds_15_30006 : exactInterval 15 30006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30006 : oddCount 30006 15 = 11 ∧ acceleratedOrbit 15 30006 = 162233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30006) = 3 ^ 11 * m + 162233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30006.1, data_15_30006.2]

/-- Complete interval computation for depth 15, residue 30007. -/
theorem bounds_15_30007 : exactInterval 15 30007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30007 : oddCount 30007 15 = 11 ∧ acceleratedOrbit 15 30007 = 162233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30007) = 3 ^ 11 * m + 162233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30007.1, data_15_30007.2]

/-- Complete interval computation for depth 15, residue 30008. -/
theorem bounds_15_30008 : exactInterval 15 30008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30008 : oddCount 30008 15 = 8 ∧ acceleratedOrbit 15 30008 = 6011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30008) = 3 ^ 8 * m + 6011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30008.1, data_15_30008.2]

/-- Complete interval computation for depth 15, residue 30009. -/
theorem bounds_15_30009 : exactInterval 15 30009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30009 : oddCount 30009 15 = 10 ∧ acceleratedOrbit 15 30009 = 54083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30009) = 3 ^ 10 * m + 54083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30009.1, data_15_30009.2]

/-- Complete interval computation for depth 15, residue 30010. -/
theorem bounds_15_30010 : exactInterval 15 30010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30010 : oddCount 30010 15 = 8 ∧ acceleratedOrbit 15 30010 = 6011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30010) = 3 ^ 8 * m + 6011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30010.1, data_15_30010.2]

/-- Complete interval computation for depth 15, residue 30011. -/
theorem bounds_15_30011 : exactInterval 15 30011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30011 : oddCount 30011 15 = 6 ∧ acceleratedOrbit 15 30011 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30011) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30011.1, data_15_30011.2]

/-- Complete interval computation for depth 15, residue 30012. -/
theorem bounds_15_30012 : exactInterval 15 30012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30012 : oddCount 30012 15 = 8 ∧ acceleratedOrbit 15 30012 = 6011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30012) = 3 ^ 8 * m + 6011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30012.1, data_15_30012.2]

/-- Complete interval computation for depth 15, residue 30013. -/
theorem bounds_15_30013 : exactInterval 15 30013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30013 : oddCount 30013 15 = 8 ∧ acceleratedOrbit 15 30013 = 6011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30013) = 3 ^ 8 * m + 6011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30013.1, data_15_30013.2]

/-- Complete interval computation for depth 15, residue 30014. -/
theorem bounds_15_30014 : exactInterval 15 30014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30014 : oddCount 30014 15 = 8 ∧ acceleratedOrbit 15 30014 = 6010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30014) = 3 ^ 8 * m + 6010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30014.1, data_15_30014.2]

end Collatz.Research.PassageAtlas.Batch0916
