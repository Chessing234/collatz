import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0397

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12976. -/
theorem bounds_15_12976 : exactInterval 15 12976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12976 : oddCount 12976 15 = 6 ∧ acceleratedOrbit 15 12976 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12976) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12976.1, data_15_12976.2]

/-- Complete interval computation for depth 15, residue 12977. -/
theorem bounds_15_12977 : exactInterval 15 12977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12977 : oddCount 12977 15 = 6 ∧ acceleratedOrbit 15 12977 = 289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12977) = 3 ^ 6 * m + 289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12977.1, data_15_12977.2]

/-- Complete interval computation for depth 15, residue 12978. -/
theorem bounds_15_12978 : exactInterval 15 12978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12978 : oddCount 12978 15 = 6 ∧ acceleratedOrbit 15 12978 = 289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12978) = 3 ^ 6 * m + 289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12978.1, data_15_12978.2]

/-- Complete interval computation for depth 15, residue 12979. -/
theorem bounds_15_12979 : exactInterval 15 12979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12979 : oddCount 12979 15 = 6 ∧ acceleratedOrbit 15 12979 = 289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12979) = 3 ^ 6 * m + 289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12979.1, data_15_12979.2]

/-- Complete interval computation for depth 15, residue 12980. -/
theorem bounds_15_12980 : exactInterval 15 12980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12980 : oddCount 12980 15 = 6 ∧ acceleratedOrbit 15 12980 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12980) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12980.1, data_15_12980.2]

/-- Complete interval computation for depth 15, residue 12981. -/
theorem bounds_15_12981 : exactInterval 15 12981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12981 : oddCount 12981 15 = 6 ∧ acceleratedOrbit 15 12981 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12981) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12981.1, data_15_12981.2]

/-- Complete interval computation for depth 15, residue 12982. -/
theorem bounds_15_12982 : exactInterval 15 12982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12982 : oddCount 12982 15 = 9 ∧ acceleratedOrbit 15 12982 = 7802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12982) = 3 ^ 9 * m + 7802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12982.1, data_15_12982.2]

/-- Complete interval computation for depth 15, residue 12983. -/
theorem bounds_15_12983 : exactInterval 15 12983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12983 : oddCount 12983 15 = 9 ∧ acceleratedOrbit 15 12983 = 7802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12983) = 3 ^ 9 * m + 7802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12983.1, data_15_12983.2]

/-- Complete interval computation for depth 15, residue 12984. -/
theorem bounds_15_12984 : exactInterval 15 12984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12984 : oddCount 12984 15 = 6 ∧ acceleratedOrbit 15 12984 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12984) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12984.1, data_15_12984.2]

/-- Complete interval computation for depth 15, residue 12985. -/
theorem bounds_15_12985 : exactInterval 15 12985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12985 : oddCount 12985 15 = 6 ∧ acceleratedOrbit 15 12985 = 289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12985) = 3 ^ 6 * m + 289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12985.1, data_15_12985.2]

/-- Complete interval computation for depth 15, residue 12986. -/
theorem bounds_15_12986 : exactInterval 15 12986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12986 : oddCount 12986 15 = 6 ∧ acceleratedOrbit 15 12986 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12986) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12986.1, data_15_12986.2]

/-- Complete interval computation for depth 15, residue 12987. -/
theorem bounds_15_12987 : exactInterval 15 12987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12987 : oddCount 12987 15 = 11 ∧ acceleratedOrbit 15 12987 = 70226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12987) = 3 ^ 11 * m + 70226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12987.1, data_15_12987.2]

/-- Complete interval computation for depth 15, residue 12988. -/
theorem bounds_15_12988 : exactInterval 15 12988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12988 : oddCount 12988 15 = 8 ∧ acceleratedOrbit 15 12988 = 2602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12988) = 3 ^ 8 * m + 2602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12988.1, data_15_12988.2]

/-- Complete interval computation for depth 15, residue 12989. -/
theorem bounds_15_12989 : exactInterval 15 12989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12989 : oddCount 12989 15 = 8 ∧ acceleratedOrbit 15 12989 = 2602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12989) = 3 ^ 8 * m + 2602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12989.1, data_15_12989.2]

/-- Complete interval computation for depth 15, residue 12990. -/
theorem bounds_15_12990 : exactInterval 15 12990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12990 : oddCount 12990 15 = 8 ∧ acceleratedOrbit 15 12990 = 2602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12990) = 3 ^ 8 * m + 2602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12990.1, data_15_12990.2]

/-- Complete interval computation for depth 15, residue 12991. -/
theorem bounds_15_12991 : exactInterval 15 12991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12991 : oddCount 12991 15 = 11 ∧ acceleratedOrbit 15 12991 = 70237 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12991) = 3 ^ 11 * m + 70237 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12991.1, data_15_12991.2]

/-- Complete interval computation for depth 15, residue 12992. -/
theorem bounds_15_12992 : exactInterval 15 12992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12992 : oddCount 12992 15 = 5 ∧ acceleratedOrbit 15 12992 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12992) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12992.1, data_15_12992.2]

/-- Complete interval computation for depth 15, residue 12993. -/
theorem bounds_15_12993 : exactInterval 15 12993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12993 : oddCount 12993 15 = 6 ∧ acceleratedOrbit 15 12993 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12993) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12993.1, data_15_12993.2]

/-- Complete interval computation for depth 15, residue 12994. -/
theorem bounds_15_12994 : exactInterval 15 12994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12994 : oddCount 12994 15 = 8 ∧ acceleratedOrbit 15 12994 = 2603 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12994) = 3 ^ 8 * m + 2603 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12994.1, data_15_12994.2]

/-- Complete interval computation for depth 15, residue 12995. -/
theorem bounds_15_12995 : exactInterval 15 12995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12995 : oddCount 12995 15 = 8 ∧ acceleratedOrbit 15 12995 = 2603 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12995) = 3 ^ 8 * m + 2603 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12995.1, data_15_12995.2]

/-- Complete interval computation for depth 15, residue 12996. -/
theorem bounds_15_12996 : exactInterval 15 12996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12996 : oddCount 12996 15 = 6 ∧ acceleratedOrbit 15 12996 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12996) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12996.1, data_15_12996.2]

/-- Complete interval computation for depth 15, residue 12997. -/
theorem bounds_15_12997 : exactInterval 15 12997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12997 : oddCount 12997 15 = 6 ∧ acceleratedOrbit 15 12997 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12997) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12997.1, data_15_12997.2]

/-- Complete interval computation for depth 15, residue 12998. -/
theorem bounds_15_12998 : exactInterval 15 12998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12998 : oddCount 12998 15 = 6 ∧ acceleratedOrbit 15 12998 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12998) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12998.1, data_15_12998.2]

/-- Complete interval computation for depth 15, residue 12999. -/
theorem bounds_15_12999 : exactInterval 15 12999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12999 : oddCount 12999 15 = 7 ∧ acceleratedOrbit 15 12999 = 868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12999) = 3 ^ 7 * m + 868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12999.1, data_15_12999.2]

/-- Complete interval computation for depth 15, residue 13000. -/
theorem bounds_15_13000 : exactInterval 15 13000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13000 : oddCount 13000 15 = 6 ∧ acceleratedOrbit 15 13000 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13000) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13000.1, data_15_13000.2]

/-- Complete interval computation for depth 15, residue 13001. -/
theorem bounds_15_13001 : exactInterval 15 13001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13001 : oddCount 13001 15 = 8 ∧ acceleratedOrbit 15 13001 = 2605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13001) = 3 ^ 8 * m + 2605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13001.1, data_15_13001.2]

/-- Complete interval computation for depth 15, residue 13002. -/
theorem bounds_15_13002 : exactInterval 15 13002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13002 : oddCount 13002 15 = 6 ∧ acceleratedOrbit 15 13002 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13002) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13002.1, data_15_13002.2]

/-- Complete interval computation for depth 15, residue 13003. -/
theorem bounds_15_13003 : exactInterval 15 13003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13003 : oddCount 13003 15 = 8 ∧ acceleratedOrbit 15 13003 = 2605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13003) = 3 ^ 8 * m + 2605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13003.1, data_15_13003.2]

/-- Complete interval computation for depth 15, residue 13004. -/
theorem bounds_15_13004 : exactInterval 15 13004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13004 : oddCount 13004 15 = 6 ∧ acceleratedOrbit 15 13004 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13004) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13004.1, data_15_13004.2]

/-- Complete interval computation for depth 15, residue 13005. -/
theorem bounds_15_13005 : exactInterval 15 13005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13005 : oddCount 13005 15 = 6 ∧ acceleratedOrbit 15 13005 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13005) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13005.1, data_15_13005.2]

/-- Complete interval computation for depth 15, residue 13006. -/
theorem bounds_15_13006 : exactInterval 15 13006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13006 : oddCount 13006 15 = 9 ∧ acceleratedOrbit 15 13006 = 7814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13006) = 3 ^ 9 * m + 7814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13006.1, data_15_13006.2]

/-- Complete interval computation for depth 15, residue 13007. -/
theorem bounds_15_13007 : exactInterval 15 13007 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13007) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13007 : oddCount 13007 15 = 9 ∧ acceleratedOrbit 15 13007 = 7814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13007) = 3 ^ 9 * m + 7814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13007.1, data_15_13007.2]

end Collatz.Research.PassageAtlas.Batch0397
