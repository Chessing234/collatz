import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0733

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23986. -/
theorem bounds_15_23986 : exactInterval 15 23986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23986 : oddCount 23986 15 = 5 ∧ acceleratedOrbit 15 23986 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23986) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23986.1, data_15_23986.2]

/-- Complete interval computation for depth 15, residue 23987. -/
theorem bounds_15_23987 : exactInterval 15 23987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23987 : oddCount 23987 15 = 5 ∧ acceleratedOrbit 15 23987 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23987) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23987.1, data_15_23987.2]

/-- Complete interval computation for depth 15, residue 23988. -/
theorem bounds_15_23988 : exactInterval 15 23988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23988 : oddCount 23988 15 = 5 ∧ acceleratedOrbit 15 23988 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23988) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23988.1, data_15_23988.2]

/-- Complete interval computation for depth 15, residue 23989. -/
theorem bounds_15_23989 : exactInterval 15 23989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23989 : oddCount 23989 15 = 5 ∧ acceleratedOrbit 15 23989 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23989) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23989.1, data_15_23989.2]

/-- Complete interval computation for depth 15, residue 23990. -/
theorem bounds_15_23990 : exactInterval 15 23990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23990 : oddCount 23990 15 = 9 ∧ acceleratedOrbit 15 23990 = 14413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23990) = 3 ^ 9 * m + 14413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23990.1, data_15_23990.2]

/-- Complete interval computation for depth 15, residue 23991. -/
theorem bounds_15_23991 : exactInterval 15 23991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23991 : oddCount 23991 15 = 9 ∧ acceleratedOrbit 15 23991 = 14413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23991) = 3 ^ 9 * m + 14413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23991.1, data_15_23991.2]

/-- Complete interval computation for depth 15, residue 23992. -/
theorem bounds_15_23992 : exactInterval 15 23992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23992 : oddCount 23992 15 = 5 ∧ acceleratedOrbit 15 23992 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23992) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23992.1, data_15_23992.2]

/-- Complete interval computation for depth 15, residue 23993. -/
theorem bounds_15_23993 : exactInterval 15 23993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23993 : oddCount 23993 15 = 5 ∧ acceleratedOrbit 15 23993 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23993) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23993.1, data_15_23993.2]

/-- Complete interval computation for depth 15, residue 23994. -/
theorem bounds_15_23994 : exactInterval 15 23994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23994 : oddCount 23994 15 = 5 ∧ acceleratedOrbit 15 23994 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23994) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23994.1, data_15_23994.2]

/-- Complete interval computation for depth 15, residue 23995. -/
theorem bounds_15_23995 : exactInterval 15 23995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23995 : oddCount 23995 15 = 9 ∧ acceleratedOrbit 15 23995 = 14417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23995) = 3 ^ 9 * m + 14417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23995.1, data_15_23995.2]

/-- Complete interval computation for depth 15, residue 23996. -/
theorem bounds_15_23996 : exactInterval 15 23996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23996 : oddCount 23996 15 = 10 ∧ acceleratedOrbit 15 23996 = 43253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23996) = 3 ^ 10 * m + 43253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23996.1, data_15_23996.2]

/-- Complete interval computation for depth 15, residue 23997. -/
theorem bounds_15_23997 : exactInterval 15 23997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23997 : oddCount 23997 15 = 10 ∧ acceleratedOrbit 15 23997 = 43253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23997) = 3 ^ 10 * m + 43253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23997.1, data_15_23997.2]

/-- Complete interval computation for depth 15, residue 23998. -/
theorem bounds_15_23998 : exactInterval 15 23998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23998 : oddCount 23998 15 = 10 ∧ acceleratedOrbit 15 23998 = 43253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23998) = 3 ^ 10 * m + 43253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23998.1, data_15_23998.2]

/-- Complete interval computation for depth 15, residue 23999. -/
theorem bounds_15_23999 : exactInterval 15 23999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23999 : oddCount 23999 15 = 13 ∧ acceleratedOrbit 15 23999 = 1167722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23999) = 3 ^ 13 * m + 1167722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23999.1, data_15_23999.2]

/-- Complete interval computation for depth 15, residue 24000. -/
theorem bounds_15_24000 : exactInterval 15 24000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24000 : oddCount 24000 15 = 5 ∧ acceleratedOrbit 15 24000 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24000) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24000.1, data_15_24000.2]

/-- Complete interval computation for depth 15, residue 24001. -/
theorem bounds_15_24001 : exactInterval 15 24001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24001 : oddCount 24001 15 = 8 ∧ acceleratedOrbit 15 24001 = 4807 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24001) = 3 ^ 8 * m + 4807 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24001.1, data_15_24001.2]

/-- Complete interval computation for depth 15, residue 24002. -/
theorem bounds_15_24002 : exactInterval 15 24002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24002 : oddCount 24002 15 = 8 ∧ acceleratedOrbit 15 24002 = 4807 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24002) = 3 ^ 8 * m + 4807 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24002.1, data_15_24002.2]

/-- Complete interval computation for depth 15, residue 24003. -/
theorem bounds_15_24003 : exactInterval 15 24003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24003 : oddCount 24003 15 = 8 ∧ acceleratedOrbit 15 24003 = 4807 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24003) = 3 ^ 8 * m + 4807 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24003.1, data_15_24003.2]

/-- Complete interval computation for depth 15, residue 24004. -/
theorem bounds_15_24004 : exactInterval 15 24004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24004 : oddCount 24004 15 = 5 ∧ acceleratedOrbit 15 24004 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24004) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24004.1, data_15_24004.2]

/-- Complete interval computation for depth 15, residue 24005. -/
theorem bounds_15_24005 : exactInterval 15 24005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24005 : oddCount 24005 15 = 5 ∧ acceleratedOrbit 15 24005 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24005) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24005.1, data_15_24005.2]

/-- Complete interval computation for depth 15, residue 24006. -/
theorem bounds_15_24006 : exactInterval 15 24006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24006 : oddCount 24006 15 = 5 ∧ acceleratedOrbit 15 24006 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24006) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24006.1, data_15_24006.2]

/-- Complete interval computation for depth 15, residue 24007. -/
theorem bounds_15_24007 : exactInterval 15 24007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24007 : oddCount 24007 15 = 8 ∧ acceleratedOrbit 15 24007 = 4808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24007) = 3 ^ 8 * m + 4808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24007.1, data_15_24007.2]

/-- Complete interval computation for depth 15, residue 24008. -/
theorem bounds_15_24008 : exactInterval 15 24008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24008 : oddCount 24008 15 = 6 ∧ acceleratedOrbit 15 24008 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24008) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24008.1, data_15_24008.2]

/-- Complete interval computation for depth 15, residue 24009. -/
theorem bounds_15_24009 : exactInterval 15 24009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24009 : oddCount 24009 15 = 7 ∧ acceleratedOrbit 15 24009 = 1603 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24009) = 3 ^ 7 * m + 1603 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24009.1, data_15_24009.2]

/-- Complete interval computation for depth 15, residue 24010. -/
theorem bounds_15_24010 : exactInterval 15 24010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24010 : oddCount 24010 15 = 6 ∧ acceleratedOrbit 15 24010 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24010) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24010.1, data_15_24010.2]

/-- Complete interval computation for depth 15, residue 24011. -/
theorem bounds_15_24011 : exactInterval 15 24011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24011 : oddCount 24011 15 = 7 ∧ acceleratedOrbit 15 24011 = 1603 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24011) = 3 ^ 7 * m + 1603 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24011.1, data_15_24011.2]

/-- Complete interval computation for depth 15, residue 24012. -/
theorem bounds_15_24012 : exactInterval 15 24012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24012 : oddCount 24012 15 = 6 ∧ acceleratedOrbit 15 24012 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24012) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24012.1, data_15_24012.2]

/-- Complete interval computation for depth 15, residue 24013. -/
theorem bounds_15_24013 : exactInterval 15 24013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24013 : oddCount 24013 15 = 6 ∧ acceleratedOrbit 15 24013 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24013) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24013.1, data_15_24013.2]

/-- Complete interval computation for depth 15, residue 24014. -/
theorem bounds_15_24014 : exactInterval 15 24014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24014 : oddCount 24014 15 = 10 ∧ acceleratedOrbit 15 24014 = 43280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24014) = 3 ^ 10 * m + 43280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24014.1, data_15_24014.2]

/-- Complete interval computation for depth 15, residue 24015. -/
theorem bounds_15_24015 : exactInterval 15 24015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24015 : oddCount 24015 15 = 10 ∧ acceleratedOrbit 15 24015 = 43280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24015) = 3 ^ 10 * m + 43280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24015.1, data_15_24015.2]

/-- Complete interval computation for depth 15, residue 24016. -/
theorem bounds_15_24016 : exactInterval 15 24016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24016 : oddCount 24016 15 = 5 ∧ acceleratedOrbit 15 24016 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24016) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24016.1, data_15_24016.2]

/-- Complete interval computation for depth 15, residue 24017. -/
theorem bounds_15_24017 : exactInterval 15 24017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24017 : oddCount 24017 15 = 6 ∧ acceleratedOrbit 15 24017 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24017) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24017.1, data_15_24017.2]

end Collatz.Research.PassageAtlas.Batch0733
