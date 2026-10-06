import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0275

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8978. -/
theorem bounds_15_8978 : exactInterval 15 8978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8978 : oddCount 8978 15 = 8 ∧ acceleratedOrbit 15 8978 = 1799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8978) = 3 ^ 8 * m + 1799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8978.1, data_15_8978.2]

/-- Complete interval computation for depth 15, residue 8979. -/
theorem bounds_15_8979 : exactInterval 15 8979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8979 : oddCount 8979 15 = 8 ∧ acceleratedOrbit 15 8979 = 1799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8979) = 3 ^ 8 * m + 1799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8979.1, data_15_8979.2]

/-- Complete interval computation for depth 15, residue 8980. -/
theorem bounds_15_8980 : exactInterval 15 8980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8980 : oddCount 8980 15 = 6 ∧ acceleratedOrbit 15 8980 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8980) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8980.1, data_15_8980.2]

/-- Complete interval computation for depth 15, residue 8981. -/
theorem bounds_15_8981 : exactInterval 15 8981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8981 : oddCount 8981 15 = 6 ∧ acceleratedOrbit 15 8981 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8981) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8981.1, data_15_8981.2]

/-- Complete interval computation for depth 15, residue 8982. -/
theorem bounds_15_8982 : exactInterval 15 8982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8982 : oddCount 8982 15 = 10 ∧ acceleratedOrbit 15 8982 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8982) = 3 ^ 10 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8982.1, data_15_8982.2]

/-- Complete interval computation for depth 15, residue 8983. -/
theorem bounds_15_8983 : exactInterval 15 8983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8983 : oddCount 8983 15 = 10 ∧ acceleratedOrbit 15 8983 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8983) = 3 ^ 10 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8983.1, data_15_8983.2]

/-- Complete interval computation for depth 15, residue 8984. -/
theorem bounds_15_8984 : exactInterval 15 8984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8984 : oddCount 8984 15 = 6 ∧ acceleratedOrbit 15 8984 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8984) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8984.1, data_15_8984.2]

/-- Complete interval computation for depth 15, residue 8985. -/
theorem bounds_15_8985 : exactInterval 15 8985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8985 : oddCount 8985 15 = 10 ∧ acceleratedOrbit 15 8985 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8985) = 3 ^ 10 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8985.1, data_15_8985.2]

/-- Complete interval computation for depth 15, residue 8986. -/
theorem bounds_15_8986 : exactInterval 15 8986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8986 : oddCount 8986 15 = 6 ∧ acceleratedOrbit 15 8986 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8986) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8986.1, data_15_8986.2]

/-- Complete interval computation for depth 15, residue 8987. -/
theorem bounds_15_8987 : exactInterval 15 8987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8987 : oddCount 8987 15 = 11 ∧ acceleratedOrbit 15 8987 = 48593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8987) = 3 ^ 11 * m + 48593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8987.1, data_15_8987.2]

/-- Complete interval computation for depth 15, residue 8988. -/
theorem bounds_15_8988 : exactInterval 15 8988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8988 : oddCount 8988 15 = 8 ∧ acceleratedOrbit 15 8988 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8988) = 3 ^ 8 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8988.1, data_15_8988.2]

/-- Complete interval computation for depth 15, residue 8989. -/
theorem bounds_15_8989 : exactInterval 15 8989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8989 : oddCount 8989 15 = 8 ∧ acceleratedOrbit 15 8989 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8989) = 3 ^ 8 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8989.1, data_15_8989.2]

/-- Complete interval computation for depth 15, residue 8990. -/
theorem bounds_15_8990 : exactInterval 15 8990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8990 : oddCount 8990 15 = 8 ∧ acceleratedOrbit 15 8990 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8990) = 3 ^ 8 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8990.1, data_15_8990.2]

/-- Complete interval computation for depth 15, residue 8991. -/
theorem bounds_15_8991 : exactInterval 15 8991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8991 : oddCount 8991 15 = 9 ∧ acceleratedOrbit 15 8991 = 5402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8991) = 3 ^ 9 * m + 5402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8991.1, data_15_8991.2]

/-- Complete interval computation for depth 15, residue 8992. -/
theorem bounds_15_8992 : exactInterval 15 8992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8992 : oddCount 8992 15 = 6 ∧ acceleratedOrbit 15 8992 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8992) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8992.1, data_15_8992.2]

/-- Complete interval computation for depth 15, residue 8993. -/
theorem bounds_15_8993 : exactInterval 15 8993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8993 : oddCount 8993 15 = 8 ∧ acceleratedOrbit 15 8993 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8993) = 3 ^ 8 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8993.1, data_15_8993.2]

/-- Complete interval computation for depth 15, residue 8994. -/
theorem bounds_15_8994 : exactInterval 15 8994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8994 : oddCount 8994 15 = 5 ∧ acceleratedOrbit 15 8994 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8994) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8994.1, data_15_8994.2]

/-- Complete interval computation for depth 15, residue 8995. -/
theorem bounds_15_8995 : exactInterval 15 8995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8995 : oddCount 8995 15 = 5 ∧ acceleratedOrbit 15 8995 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8995) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8995.1, data_15_8995.2]

/-- Complete interval computation for depth 15, residue 8996. -/
theorem bounds_15_8996 : exactInterval 15 8996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8996 : oddCount 8996 15 = 5 ∧ acceleratedOrbit 15 8996 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8996) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8996.1, data_15_8996.2]

/-- Complete interval computation for depth 15, residue 8997. -/
theorem bounds_15_8997 : exactInterval 15 8997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8997 : oddCount 8997 15 = 5 ∧ acceleratedOrbit 15 8997 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8997) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8997.1, data_15_8997.2]

/-- Complete interval computation for depth 15, residue 8998. -/
theorem bounds_15_8998 : exactInterval 15 8998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8998 : oddCount 8998 15 = 5 ∧ acceleratedOrbit 15 8998 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8998) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8998.1, data_15_8998.2]

/-- Complete interval computation for depth 15, residue 8999. -/
theorem bounds_15_8999 : exactInterval 15 8999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8999 : oddCount 8999 15 = 10 ∧ acceleratedOrbit 15 8999 = 16220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8999) = 3 ^ 10 * m + 16220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8999.1, data_15_8999.2]

/-- Complete interval computation for depth 15, residue 9000. -/
theorem bounds_15_9000 : exactInterval 15 9000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9000 : oddCount 9000 15 = 6 ∧ acceleratedOrbit 15 9000 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9000) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9000.1, data_15_9000.2]

/-- Complete interval computation for depth 15, residue 9001. -/
theorem bounds_15_9001 : exactInterval 15 9001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9001 : oddCount 9001 15 = 10 ∧ acceleratedOrbit 15 9001 = 16226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9001) = 3 ^ 10 * m + 16226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9001.1, data_15_9001.2]

/-- Complete interval computation for depth 15, residue 9002. -/
theorem bounds_15_9002 : exactInterval 15 9002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9002 : oddCount 9002 15 = 6 ∧ acceleratedOrbit 15 9002 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9002) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9002.1, data_15_9002.2]

/-- Complete interval computation for depth 15, residue 9003. -/
theorem bounds_15_9003 : exactInterval 15 9003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9003 : oddCount 9003 15 = 8 ∧ acceleratedOrbit 15 9003 = 1804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9003) = 3 ^ 8 * m + 1804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9003.1, data_15_9003.2]

/-- Complete interval computation for depth 15, residue 9004. -/
theorem bounds_15_9004 : exactInterval 15 9004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9004 : oddCount 9004 15 = 8 ∧ acceleratedOrbit 15 9004 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9004) = 3 ^ 8 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9004.1, data_15_9004.2]

/-- Complete interval computation for depth 15, residue 9005. -/
theorem bounds_15_9005 : exactInterval 15 9005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9005 : oddCount 9005 15 = 8 ∧ acceleratedOrbit 15 9005 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9005) = 3 ^ 8 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9005.1, data_15_9005.2]

/-- Complete interval computation for depth 15, residue 9006. -/
theorem bounds_15_9006 : exactInterval 15 9006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9006 : oddCount 9006 15 = 8 ∧ acceleratedOrbit 15 9006 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9006) = 3 ^ 8 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9006.1, data_15_9006.2]

/-- Complete interval computation for depth 15, residue 9007. -/
theorem bounds_15_9007 : exactInterval 15 9007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9007 : oddCount 9007 15 = 8 ∧ acceleratedOrbit 15 9007 = 1804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9007) = 3 ^ 8 * m + 1804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9007.1, data_15_9007.2]

/-- Complete interval computation for depth 15, residue 9008. -/
theorem bounds_15_9008 : exactInterval 15 9008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9008 : oddCount 9008 15 = 6 ∧ acceleratedOrbit 15 9008 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9008) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9008.1, data_15_9008.2]

/-- Complete interval computation for depth 15, residue 9009. -/
theorem bounds_15_9009 : exactInterval 15 9009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9009 : oddCount 9009 15 = 8 ∧ acceleratedOrbit 15 9009 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9009) = 3 ^ 8 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9009.1, data_15_9009.2]

/-- Complete interval computation for depth 15, residue 9010. -/
theorem bounds_15_9010 : exactInterval 15 9010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9010 : oddCount 9010 15 = 8 ∧ acceleratedOrbit 15 9010 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9010) = 3 ^ 8 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9010.1, data_15_9010.2]

end Collatz.Research.PassageAtlas.Batch0275
