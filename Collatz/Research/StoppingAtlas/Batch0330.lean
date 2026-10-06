import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0330

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1981. -/
theorem bounds_12_1981 : exactInterval 12 1981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1981 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1981) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1981 : oddCount 1981 12 = 8 ∧ acceleratedOrbit 12 1981 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1981 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1981) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1981.1, data_12_1981.2]

/-- Complete interval computation for depth 12, residue 1982. -/
theorem bounds_12_1982 : exactInterval 12 1982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1982 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1982) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1982 : oddCount 1982 12 = 8 ∧ acceleratedOrbit 12 1982 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1982 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1982) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1982.1, data_12_1982.2]

/-- Complete interval computation for depth 12, residue 1983. -/
theorem bounds_12_1983 : exactInterval 12 1983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1983 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1983) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1983 : oddCount 1983 12 = 8 ∧ acceleratedOrbit 12 1983 = 3178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1983 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1983) = 3 ^ 8 * m + 3178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1983.1, data_12_1983.2]

/-- Complete interval computation for depth 12, residue 1984. -/
theorem bounds_12_1984 : exactInterval 12 1984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1984 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1984) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1984 : oddCount 1984 12 = 5 ∧ acceleratedOrbit 12 1984 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1984 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1984) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1984.1, data_12_1984.2]

/-- Complete interval computation for depth 12, residue 1985. -/
theorem bounds_12_1985 : exactInterval 12 1985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1985 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1985) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1985 : oddCount 1985 12 = 5 ∧ acceleratedOrbit 12 1985 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1985 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1985) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1985.1, data_12_1985.2]

/-- Complete interval computation for depth 12, residue 1986. -/
theorem bounds_12_1986 : exactInterval 12 1986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1986 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1986) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1986 : oddCount 1986 12 = 7 ∧ acceleratedOrbit 12 1986 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1986 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1986) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1986.1, data_12_1986.2]

/-- Complete interval computation for depth 12, residue 1987. -/
theorem bounds_12_1987 : exactInterval 12 1987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1987 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1987) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1987 : oddCount 1987 12 = 7 ∧ acceleratedOrbit 12 1987 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1987 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1987) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1987.1, data_12_1987.2]

/-- Complete interval computation for depth 12, residue 1988. -/
theorem bounds_12_1988 : exactInterval 12 1988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1988 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1988) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1988 : oddCount 1988 12 = 4 ∧ acceleratedOrbit 12 1988 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1988 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1988) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1988.1, data_12_1988.2]

/-- Complete interval computation for depth 12, residue 1989. -/
theorem bounds_12_1989 : exactInterval 12 1989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1989 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1989) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1989 : oddCount 1989 12 = 4 ∧ acceleratedOrbit 12 1989 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1989 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1989) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1989.1, data_12_1989.2]

/-- Complete interval computation for depth 12, residue 1990. -/
theorem bounds_12_1990 : exactInterval 12 1990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1990 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1990) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1990 : oddCount 1990 12 = 4 ∧ acceleratedOrbit 12 1990 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1990 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1990) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1990.1, data_12_1990.2]

/-- Complete interval computation for depth 12, residue 1991. -/
theorem bounds_12_1991 : exactInterval 12 1991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1991 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1991) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1991 : oddCount 1991 12 = 7 ∧ acceleratedOrbit 12 1991 = 1064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1991 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1991) = 3 ^ 7 * m + 1064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1991.1, data_12_1991.2]

/-- Complete interval computation for depth 12, residue 1992. -/
theorem bounds_12_1992 : exactInterval 12 1992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1992 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1992) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1992 : oddCount 1992 12 = 5 ∧ acceleratedOrbit 12 1992 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1992 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1992) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1992.1, data_12_1992.2]

/-- Complete interval computation for depth 12, residue 1993. -/
theorem bounds_12_1993 : exactInterval 12 1993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1993 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1993) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1993 : oddCount 1993 12 = 7 ∧ acceleratedOrbit 12 1993 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1993 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1993) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1993.1, data_12_1993.2]

/-- Complete interval computation for depth 12, residue 1994. -/
theorem bounds_12_1994 : exactInterval 12 1994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1994 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1994) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1994 : oddCount 1994 12 = 5 ∧ acceleratedOrbit 12 1994 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1994 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1994) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1994.1, data_12_1994.2]

/-- Complete interval computation for depth 12, residue 1995. -/
theorem bounds_12_1995 : exactInterval 12 1995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1995 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1995) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1995 : oddCount 1995 12 = 5 ∧ acceleratedOrbit 12 1995 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1995 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1995) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1995.1, data_12_1995.2]

end Collatz.Research.StoppingAtlas.Batch0330
