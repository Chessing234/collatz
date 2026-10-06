import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0214

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6979. -/
theorem bounds_15_6979 : exactInterval 15 6979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6979 : oddCount 6979 15 = 8 ∧ acceleratedOrbit 15 6979 = 1399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6979) = 3 ^ 8 * m + 1399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6979.1, data_15_6979.2]

/-- Complete interval computation for depth 15, residue 6980. -/
theorem bounds_15_6980 : exactInterval 15 6980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6980 : oddCount 6980 15 = 8 ∧ acceleratedOrbit 15 6980 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6980) = 3 ^ 8 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6980.1, data_15_6980.2]

/-- Complete interval computation for depth 15, residue 6981. -/
theorem bounds_15_6981 : exactInterval 15 6981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6981 : oddCount 6981 15 = 8 ∧ acceleratedOrbit 15 6981 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6981) = 3 ^ 8 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6981.1, data_15_6981.2]

/-- Complete interval computation for depth 15, residue 6982. -/
theorem bounds_15_6982 : exactInterval 15 6982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6982 : oddCount 6982 15 = 8 ∧ acceleratedOrbit 15 6982 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6982) = 3 ^ 8 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6982.1, data_15_6982.2]

/-- Complete interval computation for depth 15, residue 6983. -/
theorem bounds_15_6983 : exactInterval 15 6983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6983 : oddCount 6983 15 = 9 ∧ acceleratedOrbit 15 6983 = 4196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6983) = 3 ^ 9 * m + 4196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6983.1, data_15_6983.2]

/-- Complete interval computation for depth 15, residue 6984. -/
theorem bounds_15_6984 : exactInterval 15 6984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6984 : oddCount 6984 15 = 8 ∧ acceleratedOrbit 15 6984 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6984) = 3 ^ 8 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6984.1, data_15_6984.2]

/-- Complete interval computation for depth 15, residue 6985. -/
theorem bounds_15_6985 : exactInterval 15 6985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6985 : oddCount 6985 15 = 7 ∧ acceleratedOrbit 15 6985 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6985) = 3 ^ 7 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6985.1, data_15_6985.2]

/-- Complete interval computation for depth 15, residue 6986. -/
theorem bounds_15_6986 : exactInterval 15 6986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6986 : oddCount 6986 15 = 8 ∧ acceleratedOrbit 15 6986 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6986) = 3 ^ 8 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6986.1, data_15_6986.2]

/-- Complete interval computation for depth 15, residue 6987. -/
theorem bounds_15_6987 : exactInterval 15 6987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6987 : oddCount 6987 15 = 8 ∧ acceleratedOrbit 15 6987 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6987) = 3 ^ 8 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6987.1, data_15_6987.2]

/-- Complete interval computation for depth 15, residue 6988. -/
theorem bounds_15_6988 : exactInterval 15 6988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6988 : oddCount 6988 15 = 8 ∧ acceleratedOrbit 15 6988 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6988) = 3 ^ 8 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6988.1, data_15_6988.2]

/-- Complete interval computation for depth 15, residue 6989. -/
theorem bounds_15_6989 : exactInterval 15 6989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6989 : oddCount 6989 15 = 8 ∧ acceleratedOrbit 15 6989 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6989) = 3 ^ 8 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6989.1, data_15_6989.2]

/-- Complete interval computation for depth 15, residue 6990. -/
theorem bounds_15_6990 : exactInterval 15 6990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6990 : oddCount 6990 15 = 9 ∧ acceleratedOrbit 15 6990 = 4202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6990) = 3 ^ 9 * m + 4202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6990.1, data_15_6990.2]

/-- Complete interval computation for depth 15, residue 6991. -/
theorem bounds_15_6991 : exactInterval 15 6991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6991 : oddCount 6991 15 = 9 ∧ acceleratedOrbit 15 6991 = 4202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6991) = 3 ^ 9 * m + 4202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6991.1, data_15_6991.2]

/-- Complete interval computation for depth 15, residue 6992. -/
theorem bounds_15_6992 : exactInterval 15 6992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6992 : oddCount 6992 15 = 6 ∧ acceleratedOrbit 15 6992 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6992) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6992.1, data_15_6992.2]

/-- Complete interval computation for depth 15, residue 6993. -/
theorem bounds_15_6993 : exactInterval 15 6993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6993 : oddCount 6993 15 = 7 ∧ acceleratedOrbit 15 6993 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6993) = 3 ^ 7 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6993.1, data_15_6993.2]

/-- Complete interval computation for depth 15, residue 6994. -/
theorem bounds_15_6994 : exactInterval 15 6994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6994 : oddCount 6994 15 = 7 ∧ acceleratedOrbit 15 6994 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6994) = 3 ^ 7 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6994.1, data_15_6994.2]

/-- Complete interval computation for depth 15, residue 6995. -/
theorem bounds_15_6995 : exactInterval 15 6995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6995 : oddCount 6995 15 = 7 ∧ acceleratedOrbit 15 6995 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6995) = 3 ^ 7 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6995.1, data_15_6995.2]

/-- Complete interval computation for depth 15, residue 6996. -/
theorem bounds_15_6996 : exactInterval 15 6996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6996 : oddCount 6996 15 = 6 ∧ acceleratedOrbit 15 6996 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6996) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6996.1, data_15_6996.2]

/-- Complete interval computation for depth 15, residue 6997. -/
theorem bounds_15_6997 : exactInterval 15 6997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6997 : oddCount 6997 15 = 6 ∧ acceleratedOrbit 15 6997 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6997) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6997.1, data_15_6997.2]

/-- Complete interval computation for depth 15, residue 6998. -/
theorem bounds_15_6998 : exactInterval 15 6998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6998 : oddCount 6998 15 = 9 ∧ acceleratedOrbit 15 6998 = 4207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6998) = 3 ^ 9 * m + 4207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6998.1, data_15_6998.2]

/-- Complete interval computation for depth 15, residue 6999. -/
theorem bounds_15_6999 : exactInterval 15 6999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6999 : oddCount 6999 15 = 9 ∧ acceleratedOrbit 15 6999 = 4207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6999) = 3 ^ 9 * m + 4207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6999.1, data_15_6999.2]

/-- Complete interval computation for depth 15, residue 7000. -/
theorem bounds_15_7000 : exactInterval 15 7000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7000 : oddCount 7000 15 = 5 ∧ acceleratedOrbit 15 7000 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7000) = 3 ^ 5 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7000.1, data_15_7000.2]

/-- Complete interval computation for depth 15, residue 7001. -/
theorem bounds_15_7001 : exactInterval 15 7001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7001 : oddCount 7001 15 = 5 ∧ acceleratedOrbit 15 7001 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7001) = 3 ^ 5 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7001.1, data_15_7001.2]

/-- Complete interval computation for depth 15, residue 7002. -/
theorem bounds_15_7002 : exactInterval 15 7002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7002 : oddCount 7002 15 = 5 ∧ acceleratedOrbit 15 7002 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7002) = 3 ^ 5 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7002.1, data_15_7002.2]

/-- Complete interval computation for depth 15, residue 7003. -/
theorem bounds_15_7003 : exactInterval 15 7003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7003 : oddCount 7003 15 = 8 ∧ acceleratedOrbit 15 7003 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7003) = 3 ^ 8 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7003.1, data_15_7003.2]

/-- Complete interval computation for depth 15, residue 7004. -/
theorem bounds_15_7004 : exactInterval 15 7004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7004 : oddCount 7004 15 = 5 ∧ acceleratedOrbit 15 7004 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7004) = 3 ^ 5 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7004.1, data_15_7004.2]

/-- Complete interval computation for depth 15, residue 7005. -/
theorem bounds_15_7005 : exactInterval 15 7005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7005 : oddCount 7005 15 = 5 ∧ acceleratedOrbit 15 7005 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7005) = 3 ^ 5 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7005.1, data_15_7005.2]

/-- Complete interval computation for depth 15, residue 7006. -/
theorem bounds_15_7006 : exactInterval 15 7006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7006 : oddCount 7006 15 = 10 ∧ acceleratedOrbit 15 7006 = 12635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7006) = 3 ^ 10 * m + 12635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7006.1, data_15_7006.2]

/-- Complete interval computation for depth 15, residue 7007. -/
theorem bounds_15_7007 : exactInterval 15 7007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7007 : oddCount 7007 15 = 10 ∧ acceleratedOrbit 15 7007 = 12635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7007) = 3 ^ 10 * m + 12635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7007.1, data_15_7007.2]

/-- Complete interval computation for depth 15, residue 7008. -/
theorem bounds_15_7008 : exactInterval 15 7008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7008 : oddCount 7008 15 = 6 ∧ acceleratedOrbit 15 7008 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7008) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7008.1, data_15_7008.2]

/-- Complete interval computation for depth 15, residue 7009. -/
theorem bounds_15_7009 : exactInterval 15 7009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7009 : oddCount 7009 15 = 12 ∧ acceleratedOrbit 15 7009 = 113723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7009) = 3 ^ 12 * m + 113723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7009.1, data_15_7009.2]

/-- Complete interval computation for depth 15, residue 7010. -/
theorem bounds_15_7010 : exactInterval 15 7010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7010 : oddCount 7010 15 = 6 ∧ acceleratedOrbit 15 7010 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7010) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7010.1, data_15_7010.2]

/-- Complete interval computation for depth 15, residue 7011. -/
theorem bounds_15_7011 : exactInterval 15 7011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7011 : oddCount 7011 15 = 6 ∧ acceleratedOrbit 15 7011 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7011) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7011.1, data_15_7011.2]

end Collatz.Research.PassageAtlas.Batch0214
