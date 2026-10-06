import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0922

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6978. -/
theorem bounds_13_6978 : exactInterval 13 6978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6978 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6978) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6978 : oddCount 6978 13 = 7 ∧ acceleratedOrbit 13 6978 = 1865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6978 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6978) = 3 ^ 7 * m + 1865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6978.1, data_13_6978.2]

/-- Complete interval computation for depth 13, residue 6979. -/
theorem bounds_13_6979 : exactInterval 13 6979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6979 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6979) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6979 : oddCount 6979 13 = 7 ∧ acceleratedOrbit 13 6979 = 1865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6979 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6979) = 3 ^ 7 * m + 1865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6979.1, data_13_6979.2]

/-- Complete interval computation for depth 13, residue 6980. -/
theorem bounds_13_6980 : exactInterval 13 6980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6980 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6980) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6980 : oddCount 6980 13 = 6 ∧ acceleratedOrbit 13 6980 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6980 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6980) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6980.1, data_13_6980.2]

/-- Complete interval computation for depth 13, residue 6981. -/
theorem bounds_13_6981 : exactInterval 13 6981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6981 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6981) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6981 : oddCount 6981 13 = 6 ∧ acceleratedOrbit 13 6981 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6981 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6981) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6981.1, data_13_6981.2]

/-- Complete interval computation for depth 13, residue 6982. -/
theorem bounds_13_6982 : exactInterval 13 6982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6982 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6982) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6982 : oddCount 6982 13 = 6 ∧ acceleratedOrbit 13 6982 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6982 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6982) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6982.1, data_13_6982.2]

/-- Complete interval computation for depth 13, residue 6983. -/
theorem bounds_13_6983 : exactInterval 13 6983 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6983 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6983) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6983 : oddCount 6983 13 = 8 ∧ acceleratedOrbit 13 6983 = 5594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6983 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6983) = 3 ^ 8 * m + 5594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6983.1, data_13_6983.2]

/-- Complete interval computation for depth 13, residue 6984. -/
theorem bounds_13_6984 : exactInterval 13 6984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6984 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6984) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6984 : oddCount 6984 13 = 6 ∧ acceleratedOrbit 13 6984 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6984 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6984) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6984.1, data_13_6984.2]

/-- Complete interval computation for depth 13, residue 6985. -/
theorem bounds_13_6985 : exactInterval 13 6985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6985 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6985) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6985 : oddCount 6985 13 = 6 ∧ acceleratedOrbit 13 6985 = 622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6985 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6985) = 3 ^ 6 * m + 622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6985.1, data_13_6985.2]

/-- Complete interval computation for depth 13, residue 6986. -/
theorem bounds_13_6986 : exactInterval 13 6986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6986 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6986) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6986 : oddCount 6986 13 = 6 ∧ acceleratedOrbit 13 6986 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6986 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6986) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6986.1, data_13_6986.2]

/-- Complete interval computation for depth 13, residue 6987. -/
theorem bounds_13_6987 : exactInterval 13 6987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6987 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6987) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6987 : oddCount 6987 13 = 6 ∧ acceleratedOrbit 13 6987 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6987 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6987) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6987.1, data_13_6987.2]

/-- Complete interval computation for depth 13, residue 6988. -/
theorem bounds_13_6988 : exactInterval 13 6988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6988 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6988) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6988 : oddCount 6988 13 = 6 ∧ acceleratedOrbit 13 6988 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6988 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6988) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6988.1, data_13_6988.2]

/-- Complete interval computation for depth 13, residue 6989. -/
theorem bounds_13_6989 : exactInterval 13 6989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6989 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6989) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6989 : oddCount 6989 13 = 6 ∧ acceleratedOrbit 13 6989 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6989 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6989) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6989.1, data_13_6989.2]

/-- Complete interval computation for depth 13, residue 6990. -/
theorem bounds_13_6990 : exactInterval 13 6990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6990 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6990) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6990 : oddCount 6990 13 = 7 ∧ acceleratedOrbit 13 6990 = 1867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6990 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6990) = 3 ^ 7 * m + 1867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6990.1, data_13_6990.2]

/-- Complete interval computation for depth 13, residue 6991. -/
theorem bounds_13_6991 : exactInterval 13 6991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6991 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6991) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6991 : oddCount 6991 13 = 7 ∧ acceleratedOrbit 13 6991 = 1867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6991 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6991) = 3 ^ 7 * m + 1867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6991.1, data_13_6991.2]

/-- Complete interval computation for depth 13, residue 6992. -/
theorem bounds_13_6992 : exactInterval 13 6992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6992 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6992) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6992 : oddCount 6992 13 = 4 ∧ acceleratedOrbit 13 6992 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6992 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6992) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6992.1, data_13_6992.2]

end Collatz.Research.StoppingAtlas.Batch0922
