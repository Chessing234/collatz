import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0458

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14974. -/
theorem bounds_15_14974 : exactInterval 15 14974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14974 : oddCount 14974 15 = 9 ∧ acceleratedOrbit 15 14974 = 8996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14974) = 3 ^ 9 * m + 8996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14974.1, data_15_14974.2]

/-- Complete interval computation for depth 15, residue 14975. -/
theorem bounds_15_14975 : exactInterval 15 14975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14975 : oddCount 14975 15 = 11 ∧ acceleratedOrbit 15 14975 = 80963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14975) = 3 ^ 11 * m + 80963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14975.1, data_15_14975.2]

/-- Complete interval computation for depth 15, residue 14976. -/
theorem bounds_15_14976 : exactInterval 15 14976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14976 : oddCount 14976 15 = 3 ∧ acceleratedOrbit 15 14976 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14976) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14976.1, data_15_14976.2]

/-- Complete interval computation for depth 15, residue 14977. -/
theorem bounds_15_14977 : exactInterval 15 14977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14977 : oddCount 14977 15 = 9 ∧ acceleratedOrbit 15 14977 = 8999 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14977) = 3 ^ 9 * m + 8999 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14977.1, data_15_14977.2]

/-- Complete interval computation for depth 15, residue 14978. -/
theorem bounds_15_14978 : exactInterval 15 14978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14978 : oddCount 14978 15 = 6 ∧ acceleratedOrbit 15 14978 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14978) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14978.1, data_15_14978.2]

/-- Complete interval computation for depth 15, residue 14979. -/
theorem bounds_15_14979 : exactInterval 15 14979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14979 : oddCount 14979 15 = 6 ∧ acceleratedOrbit 15 14979 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14979) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14979.1, data_15_14979.2]

/-- Complete interval computation for depth 15, residue 14980. -/
theorem bounds_15_14980 : exactInterval 15 14980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14980 : oddCount 14980 15 = 7 ∧ acceleratedOrbit 15 14980 = 1001 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14980) = 3 ^ 7 * m + 1001 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14980.1, data_15_14980.2]

/-- Complete interval computation for depth 15, residue 14981. -/
theorem bounds_15_14981 : exactInterval 15 14981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14981 : oddCount 14981 15 = 7 ∧ acceleratedOrbit 15 14981 = 1001 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14981) = 3 ^ 7 * m + 1001 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14981.1, data_15_14981.2]

/-- Complete interval computation for depth 15, residue 14982. -/
theorem bounds_15_14982 : exactInterval 15 14982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14982 : oddCount 14982 15 = 7 ∧ acceleratedOrbit 15 14982 = 1001 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14982) = 3 ^ 7 * m + 1001 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14982.1, data_15_14982.2]

/-- Complete interval computation for depth 15, residue 14983. -/
theorem bounds_15_14983 : exactInterval 15 14983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14983 : oddCount 14983 15 = 7 ∧ acceleratedOrbit 15 14983 = 1001 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14983) = 3 ^ 7 * m + 1001 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14983.1, data_15_14983.2]

/-- Complete interval computation for depth 15, residue 14984. -/
theorem bounds_15_14984 : exactInterval 15 14984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14984 : oddCount 14984 15 = 6 ∧ acceleratedOrbit 15 14984 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14984) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14984.1, data_15_14984.2]

/-- Complete interval computation for depth 15, residue 14985. -/
theorem bounds_15_14985 : exactInterval 15 14985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14985 : oddCount 14985 15 = 8 ∧ acceleratedOrbit 15 14985 = 3001 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14985) = 3 ^ 8 * m + 3001 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14985.1, data_15_14985.2]

/-- Complete interval computation for depth 15, residue 14986. -/
theorem bounds_15_14986 : exactInterval 15 14986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14986 : oddCount 14986 15 = 6 ∧ acceleratedOrbit 15 14986 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14986) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14986.1, data_15_14986.2]

/-- Complete interval computation for depth 15, residue 14987. -/
theorem bounds_15_14987 : exactInterval 15 14987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14987 : oddCount 14987 15 = 7 ∧ acceleratedOrbit 15 14987 = 1001 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14987) = 3 ^ 7 * m + 1001 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14987.1, data_15_14987.2]

/-- Complete interval computation for depth 15, residue 14988. -/
theorem bounds_15_14988 : exactInterval 15 14988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14988 : oddCount 14988 15 = 6 ∧ acceleratedOrbit 15 14988 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14988) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14988.1, data_15_14988.2]

/-- Complete interval computation for depth 15, residue 14989. -/
theorem bounds_15_14989 : exactInterval 15 14989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14989 : oddCount 14989 15 = 6 ∧ acceleratedOrbit 15 14989 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14989) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14989.1, data_15_14989.2]

/-- Complete interval computation for depth 15, residue 14990. -/
theorem bounds_15_14990 : exactInterval 15 14990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14990 : oddCount 14990 15 = 8 ∧ acceleratedOrbit 15 14990 = 3002 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14990) = 3 ^ 8 * m + 3002 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14990.1, data_15_14990.2]

/-- Complete interval computation for depth 15, residue 14991. -/
theorem bounds_15_14991 : exactInterval 15 14991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14991 : oddCount 14991 15 = 8 ∧ acceleratedOrbit 15 14991 = 3002 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14991) = 3 ^ 8 * m + 3002 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14991.1, data_15_14991.2]

/-- Complete interval computation for depth 15, residue 14992. -/
theorem bounds_15_14992 : exactInterval 15 14992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14992 : oddCount 14992 15 = 8 ∧ acceleratedOrbit 15 14992 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14992) = 3 ^ 8 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14992.1, data_15_14992.2]

/-- Complete interval computation for depth 15, residue 14993. -/
theorem bounds_15_14993 : exactInterval 15 14993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14993 : oddCount 14993 15 = 9 ∧ acceleratedOrbit 15 14993 = 9011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14993) = 3 ^ 9 * m + 9011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14993.1, data_15_14993.2]

/-- Complete interval computation for depth 15, residue 14994. -/
theorem bounds_15_14994 : exactInterval 15 14994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14994 : oddCount 14994 15 = 9 ∧ acceleratedOrbit 15 14994 = 9011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14994) = 3 ^ 9 * m + 9011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14994.1, data_15_14994.2]

/-- Complete interval computation for depth 15, residue 14995. -/
theorem bounds_15_14995 : exactInterval 15 14995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14995 : oddCount 14995 15 = 9 ∧ acceleratedOrbit 15 14995 = 9011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14995) = 3 ^ 9 * m + 9011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14995.1, data_15_14995.2]

/-- Complete interval computation for depth 15, residue 14996. -/
theorem bounds_15_14996 : exactInterval 15 14996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14996 : oddCount 14996 15 = 8 ∧ acceleratedOrbit 15 14996 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14996) = 3 ^ 8 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14996.1, data_15_14996.2]

/-- Complete interval computation for depth 15, residue 14997. -/
theorem bounds_15_14997 : exactInterval 15 14997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14997 : oddCount 14997 15 = 8 ∧ acceleratedOrbit 15 14997 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14997) = 3 ^ 8 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14997.1, data_15_14997.2]

/-- Complete interval computation for depth 15, residue 14998. -/
theorem bounds_15_14998 : exactInterval 15 14998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14998 : oddCount 14998 15 = 6 ∧ acceleratedOrbit 15 14998 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14998) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14998.1, data_15_14998.2]

/-- Complete interval computation for depth 15, residue 14999. -/
theorem bounds_15_14999 : exactInterval 15 14999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14999 : oddCount 14999 15 = 6 ∧ acceleratedOrbit 15 14999 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14999) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14999.1, data_15_14999.2]

/-- Complete interval computation for depth 15, residue 15000. -/
theorem bounds_15_15000 : exactInterval 15 15000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15000 : oddCount 15000 15 = 8 ∧ acceleratedOrbit 15 15000 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15000) = 3 ^ 8 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15000.1, data_15_15000.2]

/-- Complete interval computation for depth 15, residue 15001. -/
theorem bounds_15_15001 : exactInterval 15 15001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15001 : oddCount 15001 15 = 8 ∧ acceleratedOrbit 15 15001 = 3005 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15001) = 3 ^ 8 * m + 3005 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15001.1, data_15_15001.2]

/-- Complete interval computation for depth 15, residue 15002. -/
theorem bounds_15_15002 : exactInterval 15 15002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15002 : oddCount 15002 15 = 8 ∧ acceleratedOrbit 15 15002 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15002) = 3 ^ 8 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15002.1, data_15_15002.2]

/-- Complete interval computation for depth 15, residue 15003. -/
theorem bounds_15_15003 : exactInterval 15 15003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15003 : oddCount 15003 15 = 12 ∧ acceleratedOrbit 15 15003 = 243350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15003) = 3 ^ 12 * m + 243350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15003.1, data_15_15003.2]

/-- Complete interval computation for depth 15, residue 15004. -/
theorem bounds_15_15004 : exactInterval 15 15004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15004 : oddCount 15004 15 = 9 ∧ acceleratedOrbit 15 15004 = 9017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15004) = 3 ^ 9 * m + 9017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15004.1, data_15_15004.2]

/-- Complete interval computation for depth 15, residue 15005. -/
theorem bounds_15_15005 : exactInterval 15 15005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15005 : oddCount 15005 15 = 9 ∧ acceleratedOrbit 15 15005 = 9017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15005) = 3 ^ 9 * m + 9017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15005.1, data_15_15005.2]

/-- Complete interval computation for depth 15, residue 15006. -/
theorem bounds_15_15006 : exactInterval 15 15006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15006 : oddCount 15006 15 = 9 ∧ acceleratedOrbit 15 15006 = 9017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15006) = 3 ^ 9 * m + 9017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15006.1, data_15_15006.2]

end Collatz.Research.PassageAtlas.Batch0458
