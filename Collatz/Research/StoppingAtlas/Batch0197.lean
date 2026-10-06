import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0197

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1986. -/
theorem bounds_11_1986 : exactInterval 11 1986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1986 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1986) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1986 : oddCount 1986 11 = 7 ∧ acceleratedOrbit 11 1986 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1986 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1986) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1986.1, data_11_1986.2]

/-- Complete interval computation for depth 11, residue 1987. -/
theorem bounds_11_1987 : exactInterval 11 1987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1987 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1987) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1987 : oddCount 1987 11 = 7 ∧ acceleratedOrbit 11 1987 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1987 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1987) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1987.1, data_11_1987.2]

/-- Complete interval computation for depth 11, residue 1988. -/
theorem bounds_11_1988 : exactInterval 11 1988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1988 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1988) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1988 : oddCount 1988 11 = 4 ∧ acceleratedOrbit 11 1988 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1988 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1988) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1988.1, data_11_1988.2]

/-- Complete interval computation for depth 11, residue 1989. -/
theorem bounds_11_1989 : exactInterval 11 1989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1989 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1989) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1989 : oddCount 1989 11 = 4 ∧ acceleratedOrbit 11 1989 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1989 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1989) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1989.1, data_11_1989.2]

/-- Complete interval computation for depth 11, residue 1990. -/
theorem bounds_11_1990 : exactInterval 11 1990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1990 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1990) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1990 : oddCount 1990 11 = 4 ∧ acceleratedOrbit 11 1990 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1990 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1990) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1990.1, data_11_1990.2]

/-- Complete interval computation for depth 11, residue 1991. -/
theorem bounds_11_1991 : exactInterval 11 1991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1991 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1991) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1991 : oddCount 1991 11 = 7 ∧ acceleratedOrbit 11 1991 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1991 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1991) = 3 ^ 7 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1991.1, data_11_1991.2]

/-- Complete interval computation for depth 11, residue 1992. -/
theorem bounds_11_1992 : exactInterval 11 1992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1992 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1992) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1992 : oddCount 1992 11 = 5 ∧ acceleratedOrbit 11 1992 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1992 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1992) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1992.1, data_11_1992.2]

/-- Complete interval computation for depth 11, residue 1993. -/
theorem bounds_11_1993 : exactInterval 11 1993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1993 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1993) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1993 : oddCount 1993 11 = 7 ∧ acceleratedOrbit 11 1993 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1993 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1993) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1993.1, data_11_1993.2]

/-- Complete interval computation for depth 11, residue 1994. -/
theorem bounds_11_1994 : exactInterval 11 1994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1994 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1994) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1994 : oddCount 1994 11 = 5 ∧ acceleratedOrbit 11 1994 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1994 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1994) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1994.1, data_11_1994.2]

/-- Complete interval computation for depth 11, residue 1995. -/
theorem bounds_11_1995 : exactInterval 11 1995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1995 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1995) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1995 : oddCount 1995 11 = 4 ∧ acceleratedOrbit 11 1995 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1995 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1995) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1995.1, data_11_1995.2]

/-- Complete interval computation for depth 11, residue 1996. -/
theorem bounds_11_1996 : exactInterval 11 1996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1996 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1996) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1996 : oddCount 1996 11 = 5 ∧ acceleratedOrbit 11 1996 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1996 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1996) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1996.1, data_11_1996.2]

/-- Complete interval computation for depth 11, residue 1997. -/
theorem bounds_11_1997 : exactInterval 11 1997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1997 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1997) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1997 : oddCount 1997 11 = 5 ∧ acceleratedOrbit 11 1997 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1997 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1997) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1997.1, data_11_1997.2]

/-- Complete interval computation for depth 11, residue 1998. -/
theorem bounds_11_1998 : exactInterval 11 1998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1998 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1998) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1998 : oddCount 1998 11 = 6 ∧ acceleratedOrbit 11 1998 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1998 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1998) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1998.1, data_11_1998.2]

/-- Complete interval computation for depth 11, residue 1999. -/
theorem bounds_11_1999 : exactInterval 11 1999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1999 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1999) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1999 : oddCount 1999 11 = 6 ∧ acceleratedOrbit 11 1999 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1999 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1999) = 3 ^ 6 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1999.1, data_11_1999.2]

/-- Complete interval computation for depth 11, residue 2000. -/
theorem bounds_11_2000 : exactInterval 11 2000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2000 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2000) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2000 : oddCount 2000 11 = 5 ∧ acceleratedOrbit 11 2000 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2000 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2000) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2000.1, data_11_2000.2]

end Collatz.Research.StoppingAtlas.Batch0197
