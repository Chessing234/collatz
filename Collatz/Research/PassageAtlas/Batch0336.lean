import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0336

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10977. -/
theorem bounds_15_10977 : exactInterval 15 10977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10977 : oddCount 10977 15 = 10 ∧ acceleratedOrbit 15 10977 = 19786 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10977) = 3 ^ 10 * m + 19786 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10977.1, data_15_10977.2]

/-- Complete interval computation for depth 15, residue 10978. -/
theorem bounds_15_10978 : exactInterval 15 10978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10978 : oddCount 10978 15 = 5 ∧ acceleratedOrbit 15 10978 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10978) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10978.1, data_15_10978.2]

/-- Complete interval computation for depth 15, residue 10979. -/
theorem bounds_15_10979 : exactInterval 15 10979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10979 : oddCount 10979 15 = 5 ∧ acceleratedOrbit 15 10979 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10979) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10979.1, data_15_10979.2]

/-- Complete interval computation for depth 15, residue 10980. -/
theorem bounds_15_10980 : exactInterval 15 10980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10980 : oddCount 10980 15 = 6 ∧ acceleratedOrbit 15 10980 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10980) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10980.1, data_15_10980.2]

/-- Complete interval computation for depth 15, residue 10981. -/
theorem bounds_15_10981 : exactInterval 15 10981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10981 : oddCount 10981 15 = 6 ∧ acceleratedOrbit 15 10981 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10981) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10981.1, data_15_10981.2]

/-- Complete interval computation for depth 15, residue 10982. -/
theorem bounds_15_10982 : exactInterval 15 10982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10982 : oddCount 10982 15 = 6 ∧ acceleratedOrbit 15 10982 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10982) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10982.1, data_15_10982.2]

/-- Complete interval computation for depth 15, residue 10983. -/
theorem bounds_15_10983 : exactInterval 15 10983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10983 : oddCount 10983 15 = 11 ∧ acceleratedOrbit 15 10983 = 59383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10983) = 3 ^ 11 * m + 59383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10983.1, data_15_10983.2]

/-- Complete interval computation for depth 15, residue 10984. -/
theorem bounds_15_10984 : exactInterval 15 10984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10984 : oddCount 10984 15 = 5 ∧ acceleratedOrbit 15 10984 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10984) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10984.1, data_15_10984.2]

/-- Complete interval computation for depth 15, residue 10985. -/
theorem bounds_15_10985 : exactInterval 15 10985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10985 : oddCount 10985 15 = 11 ∧ acceleratedOrbit 15 10985 = 59399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10985) = 3 ^ 11 * m + 59399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10985.1, data_15_10985.2]

/-- Complete interval computation for depth 15, residue 10986. -/
theorem bounds_15_10986 : exactInterval 15 10986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10986 : oddCount 10986 15 = 5 ∧ acceleratedOrbit 15 10986 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10986) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10986.1, data_15_10986.2]

/-- Complete interval computation for depth 15, residue 10987. -/
theorem bounds_15_10987 : exactInterval 15 10987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10987 : oddCount 10987 15 = 10 ∧ acceleratedOrbit 15 10987 = 19804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10987) = 3 ^ 10 * m + 19804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10987.1, data_15_10987.2]

/-- Complete interval computation for depth 15, residue 10988. -/
theorem bounds_15_10988 : exactInterval 15 10988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10988 : oddCount 10988 15 = 7 ∧ acceleratedOrbit 15 10988 = 734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10988) = 3 ^ 7 * m + 734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10988.1, data_15_10988.2]

/-- Complete interval computation for depth 15, residue 10989. -/
theorem bounds_15_10989 : exactInterval 15 10989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10989 : oddCount 10989 15 = 7 ∧ acceleratedOrbit 15 10989 = 734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10989) = 3 ^ 7 * m + 734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10989.1, data_15_10989.2]

/-- Complete interval computation for depth 15, residue 10990. -/
theorem bounds_15_10990 : exactInterval 15 10990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10990 : oddCount 10990 15 = 7 ∧ acceleratedOrbit 15 10990 = 734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10990) = 3 ^ 7 * m + 734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10990.1, data_15_10990.2]

/-- Complete interval computation for depth 15, residue 10991. -/
theorem bounds_15_10991 : exactInterval 15 10991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10991 : oddCount 10991 15 = 11 ∧ acceleratedOrbit 15 10991 = 59426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10991) = 3 ^ 11 * m + 59426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10991.1, data_15_10991.2]

/-- Complete interval computation for depth 15, residue 10992. -/
theorem bounds_15_10992 : exactInterval 15 10992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10992 : oddCount 10992 15 = 6 ∧ acceleratedOrbit 15 10992 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10992) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10992.1, data_15_10992.2]

/-- Complete interval computation for depth 15, residue 10993. -/
theorem bounds_15_10993 : exactInterval 15 10993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10993 : oddCount 10993 15 = 5 ∧ acceleratedOrbit 15 10993 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10993) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10993.1, data_15_10993.2]

/-- Complete interval computation for depth 15, residue 10994. -/
theorem bounds_15_10994 : exactInterval 15 10994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10994 : oddCount 10994 15 = 10 ∧ acceleratedOrbit 15 10994 = 19820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10994) = 3 ^ 10 * m + 19820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10994.1, data_15_10994.2]

/-- Complete interval computation for depth 15, residue 10995. -/
theorem bounds_15_10995 : exactInterval 15 10995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10995 : oddCount 10995 15 = 10 ∧ acceleratedOrbit 15 10995 = 19820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10995) = 3 ^ 10 * m + 19820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10995.1, data_15_10995.2]

/-- Complete interval computation for depth 15, residue 10996. -/
theorem bounds_15_10996 : exactInterval 15 10996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10996 : oddCount 10996 15 = 6 ∧ acceleratedOrbit 15 10996 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10996) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10996.1, data_15_10996.2]

/-- Complete interval computation for depth 15, residue 10997. -/
theorem bounds_15_10997 : exactInterval 15 10997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10997 : oddCount 10997 15 = 6 ∧ acceleratedOrbit 15 10997 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10997) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10997.1, data_15_10997.2]

/-- Complete interval computation for depth 15, residue 10998. -/
theorem bounds_15_10998 : exactInterval 15 10998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10998 : oddCount 10998 15 = 8 ∧ acceleratedOrbit 15 10998 = 2204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10998) = 3 ^ 8 * m + 2204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10998.1, data_15_10998.2]

/-- Complete interval computation for depth 15, residue 10999. -/
theorem bounds_15_10999 : exactInterval 15 10999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10999 : oddCount 10999 15 = 8 ∧ acceleratedOrbit 15 10999 = 2204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10999) = 3 ^ 8 * m + 2204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10999.1, data_15_10999.2]

/-- Complete interval computation for depth 15, residue 11000. -/
theorem bounds_15_11000 : exactInterval 15 11000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11000 : oddCount 11000 15 = 6 ∧ acceleratedOrbit 15 11000 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11000) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11000.1, data_15_11000.2]

/-- Complete interval computation for depth 15, residue 11001. -/
theorem bounds_15_11001 : exactInterval 15 11001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11001 : oddCount 11001 15 = 8 ∧ acceleratedOrbit 15 11001 = 2204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11001) = 3 ^ 8 * m + 2204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11001.1, data_15_11001.2]

/-- Complete interval computation for depth 15, residue 11002. -/
theorem bounds_15_11002 : exactInterval 15 11002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11002 : oddCount 11002 15 = 6 ∧ acceleratedOrbit 15 11002 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11002) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11002.1, data_15_11002.2]

/-- Complete interval computation for depth 15, residue 11003. -/
theorem bounds_15_11003 : exactInterval 15 11003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11003 : oddCount 11003 15 = 11 ∧ acceleratedOrbit 15 11003 = 59494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11003) = 3 ^ 11 * m + 59494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11003.1, data_15_11003.2]

/-- Complete interval computation for depth 15, residue 11004. -/
theorem bounds_15_11004 : exactInterval 15 11004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11004 : oddCount 11004 15 = 10 ∧ acceleratedOrbit 15 11004 = 19838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11004) = 3 ^ 10 * m + 19838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11004.1, data_15_11004.2]

/-- Complete interval computation for depth 15, residue 11005. -/
theorem bounds_15_11005 : exactInterval 15 11005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11005 : oddCount 11005 15 = 10 ∧ acceleratedOrbit 15 11005 = 19838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11005) = 3 ^ 10 * m + 19838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11005.1, data_15_11005.2]

/-- Complete interval computation for depth 15, residue 11006. -/
theorem bounds_15_11006 : exactInterval 15 11006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11006 : oddCount 11006 15 = 10 ∧ acceleratedOrbit 15 11006 = 19838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11006) = 3 ^ 10 * m + 19838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11006.1, data_15_11006.2]

/-- Complete interval computation for depth 15, residue 11007. -/
theorem bounds_15_11007 : exactInterval 15 11007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11007 : oddCount 11007 15 = 10 ∧ acceleratedOrbit 15 11007 = 19837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11007) = 3 ^ 10 * m + 19837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11007.1, data_15_11007.2]

/-- Complete interval computation for depth 15, residue 11008. -/
theorem bounds_15_11008 : exactInterval 15 11008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11008 : oddCount 11008 15 = 4 ∧ acceleratedOrbit 15 11008 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11008) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11008.1, data_15_11008.2]

/-- Complete interval computation for depth 15, residue 11009. -/
theorem bounds_15_11009 : exactInterval 15 11009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11009 : oddCount 11009 15 = 8 ∧ acceleratedOrbit 15 11009 = 2207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11009) = 3 ^ 8 * m + 2207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11009.1, data_15_11009.2]

end Collatz.Research.PassageAtlas.Batch0336
