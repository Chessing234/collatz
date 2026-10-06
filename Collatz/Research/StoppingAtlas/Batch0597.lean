import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0597

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1986. -/
theorem bounds_13_1986 : exactInterval 13 1986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1986 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1986) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1986 : oddCount 1986 13 = 8 ∧ acceleratedOrbit 13 1986 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1986 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1986) = 3 ^ 8 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1986.1, data_13_1986.2]

/-- Complete interval computation for depth 13, residue 1987. -/
theorem bounds_13_1987 : exactInterval 13 1987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1987 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1987) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1987 : oddCount 1987 13 = 8 ∧ acceleratedOrbit 13 1987 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1987 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1987) = 3 ^ 8 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1987.1, data_13_1987.2]

/-- Complete interval computation for depth 13, residue 1988. -/
theorem bounds_13_1988 : exactInterval 13 1988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1988 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1988) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1988 : oddCount 1988 13 = 4 ∧ acceleratedOrbit 13 1988 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1988 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1988) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1988.1, data_13_1988.2]

/-- Complete interval computation for depth 13, residue 1989. -/
theorem bounds_13_1989 : exactInterval 13 1989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1989 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1989) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1989 : oddCount 1989 13 = 4 ∧ acceleratedOrbit 13 1989 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1989 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1989) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1989.1, data_13_1989.2]

/-- Complete interval computation for depth 13, residue 1990. -/
theorem bounds_13_1990 : exactInterval 13 1990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1990 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1990) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1990 : oddCount 1990 13 = 4 ∧ acceleratedOrbit 13 1990 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1990 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1990) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1990.1, data_13_1990.2]

/-- Complete interval computation for depth 13, residue 1991. -/
theorem bounds_13_1991 : exactInterval 13 1991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1991 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1991) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1991 : oddCount 1991 13 = 7 ∧ acceleratedOrbit 13 1991 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1991 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1991) = 3 ^ 7 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1991.1, data_13_1991.2]

/-- Complete interval computation for depth 13, residue 1992. -/
theorem bounds_13_1992 : exactInterval 13 1992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1992 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1992) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1992 : oddCount 1992 13 = 6 ∧ acceleratedOrbit 13 1992 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1992 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1992) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1992.1, data_13_1992.2]

/-- Complete interval computation for depth 13, residue 1993. -/
theorem bounds_13_1993 : exactInterval 13 1993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1993 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1993) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1993 : oddCount 1993 13 = 7 ∧ acceleratedOrbit 13 1993 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1993 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1993) = 3 ^ 7 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1993.1, data_13_1993.2]

/-- Complete interval computation for depth 13, residue 1994. -/
theorem bounds_13_1994 : exactInterval 13 1994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1994 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1994) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1994 : oddCount 1994 13 = 6 ∧ acceleratedOrbit 13 1994 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1994 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1994) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1994.1, data_13_1994.2]

/-- Complete interval computation for depth 13, residue 1995. -/
theorem bounds_13_1995 : exactInterval 13 1995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1995 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1995) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1995 : oddCount 1995 13 = 6 ∧ acceleratedOrbit 13 1995 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1995 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1995) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1995.1, data_13_1995.2]

/-- Complete interval computation for depth 13, residue 1996. -/
theorem bounds_13_1996 : exactInterval 13 1996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1996 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1996) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1996 : oddCount 1996 13 = 6 ∧ acceleratedOrbit 13 1996 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1996 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1996) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1996.1, data_13_1996.2]

/-- Complete interval computation for depth 13, residue 1997. -/
theorem bounds_13_1997 : exactInterval 13 1997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1997 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1997) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1997 : oddCount 1997 13 = 6 ∧ acceleratedOrbit 13 1997 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1997 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1997) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1997.1, data_13_1997.2]

/-- Complete interval computation for depth 13, residue 1998. -/
theorem bounds_13_1998 : exactInterval 13 1998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1998 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1998) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1998 : oddCount 1998 13 = 6 ∧ acceleratedOrbit 13 1998 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1998 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1998) = 3 ^ 6 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1998.1, data_13_1998.2]

/-- Complete interval computation for depth 13, residue 1999. -/
theorem bounds_13_1999 : exactInterval 13 1999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1999 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1999) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1999 : oddCount 1999 13 = 6 ∧ acceleratedOrbit 13 1999 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1999 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1999) = 3 ^ 6 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1999.1, data_13_1999.2]

/-- Complete interval computation for depth 13, residue 2000. -/
theorem bounds_13_2000 : exactInterval 13 2000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2000 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2000) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2000 : oddCount 2000 13 = 6 ∧ acceleratedOrbit 13 2000 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2000 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2000) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2000.1, data_13_2000.2]

end Collatz.Research.StoppingAtlas.Batch0597
