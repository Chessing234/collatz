import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0763

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24969. -/
theorem bounds_15_24969 : exactInterval 15 24969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24969 : oddCount 24969 15 = 8 ∧ acceleratedOrbit 15 24969 = 5000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24969) = 3 ^ 8 * m + 5000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24969.1, data_15_24969.2]

/-- Complete interval computation for depth 15, residue 24970. -/
theorem bounds_15_24970 : exactInterval 15 24970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24970 : oddCount 24970 15 = 6 ∧ acceleratedOrbit 15 24970 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24970) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24970.1, data_15_24970.2]

/-- Complete interval computation for depth 15, residue 24971. -/
theorem bounds_15_24971 : exactInterval 15 24971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24971 : oddCount 24971 15 = 9 ∧ acceleratedOrbit 15 24971 = 15002 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24971) = 3 ^ 9 * m + 15002 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24971.1, data_15_24971.2]

/-- Complete interval computation for depth 15, residue 24972. -/
theorem bounds_15_24972 : exactInterval 15 24972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24972 : oddCount 24972 15 = 6 ∧ acceleratedOrbit 15 24972 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24972) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24972.1, data_15_24972.2]

/-- Complete interval computation for depth 15, residue 24973. -/
theorem bounds_15_24973 : exactInterval 15 24973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24973 : oddCount 24973 15 = 6 ∧ acceleratedOrbit 15 24973 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24973) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24973.1, data_15_24973.2]

/-- Complete interval computation for depth 15, residue 24974. -/
theorem bounds_15_24974 : exactInterval 15 24974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24974 : oddCount 24974 15 = 9 ∧ acceleratedOrbit 15 24974 = 15005 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24974) = 3 ^ 9 * m + 15005 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24974.1, data_15_24974.2]

/-- Complete interval computation for depth 15, residue 24975. -/
theorem bounds_15_24975 : exactInterval 15 24975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24975 : oddCount 24975 15 = 9 ∧ acceleratedOrbit 15 24975 = 15005 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24975) = 3 ^ 9 * m + 15005 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24975.1, data_15_24975.2]

/-- Complete interval computation for depth 15, residue 24976. -/
theorem bounds_15_24976 : exactInterval 15 24976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24976 : oddCount 24976 15 = 6 ∧ acceleratedOrbit 15 24976 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24976) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24976.1, data_15_24976.2]

/-- Complete interval computation for depth 15, residue 24977. -/
theorem bounds_15_24977 : exactInterval 15 24977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24977 : oddCount 24977 15 = 6 ∧ acceleratedOrbit 15 24977 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24977) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24977.1, data_15_24977.2]

/-- Complete interval computation for depth 15, residue 24978. -/
theorem bounds_15_24978 : exactInterval 15 24978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24978 : oddCount 24978 15 = 6 ∧ acceleratedOrbit 15 24978 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24978) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24978.1, data_15_24978.2]

/-- Complete interval computation for depth 15, residue 24979. -/
theorem bounds_15_24979 : exactInterval 15 24979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24979 : oddCount 24979 15 = 6 ∧ acceleratedOrbit 15 24979 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24979) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24979.1, data_15_24979.2]

/-- Complete interval computation for depth 15, residue 24980. -/
theorem bounds_15_24980 : exactInterval 15 24980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24980 : oddCount 24980 15 = 6 ∧ acceleratedOrbit 15 24980 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24980) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24980.1, data_15_24980.2]

/-- Complete interval computation for depth 15, residue 24981. -/
theorem bounds_15_24981 : exactInterval 15 24981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24981 : oddCount 24981 15 = 6 ∧ acceleratedOrbit 15 24981 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24981) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24981.1, data_15_24981.2]

/-- Complete interval computation for depth 15, residue 24982. -/
theorem bounds_15_24982 : exactInterval 15 24982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24982 : oddCount 24982 15 = 6 ∧ acceleratedOrbit 15 24982 = 556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24982) = 3 ^ 6 * m + 556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24982.1, data_15_24982.2]

/-- Complete interval computation for depth 15, residue 24983. -/
theorem bounds_15_24983 : exactInterval 15 24983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24983 : oddCount 24983 15 = 6 ∧ acceleratedOrbit 15 24983 = 556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24983) = 3 ^ 6 * m + 556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24983.1, data_15_24983.2]

/-- Complete interval computation for depth 15, residue 24984. -/
theorem bounds_15_24984 : exactInterval 15 24984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24984 : oddCount 24984 15 = 6 ∧ acceleratedOrbit 15 24984 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24984) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24984.1, data_15_24984.2]

/-- Complete interval computation for depth 15, residue 24985. -/
theorem bounds_15_24985 : exactInterval 15 24985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24985 : oddCount 24985 15 = 6 ∧ acceleratedOrbit 15 24985 = 556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24985) = 3 ^ 6 * m + 556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24985.1, data_15_24985.2]

/-- Complete interval computation for depth 15, residue 24986. -/
theorem bounds_15_24986 : exactInterval 15 24986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24986 : oddCount 24986 15 = 6 ∧ acceleratedOrbit 15 24986 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24986) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24986.1, data_15_24986.2]

/-- Complete interval computation for depth 15, residue 24987. -/
theorem bounds_15_24987 : exactInterval 15 24987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24987 : oddCount 24987 15 = 10 ∧ acceleratedOrbit 15 24987 = 45031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24987) = 3 ^ 10 * m + 45031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24987.1, data_15_24987.2]

/-- Complete interval computation for depth 15, residue 24988. -/
theorem bounds_15_24988 : exactInterval 15 24988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24988 : oddCount 24988 15 = 9 ∧ acceleratedOrbit 15 24988 = 15013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24988) = 3 ^ 9 * m + 15013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24988.1, data_15_24988.2]

/-- Complete interval computation for depth 15, residue 24989. -/
theorem bounds_15_24989 : exactInterval 15 24989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24989 : oddCount 24989 15 = 9 ∧ acceleratedOrbit 15 24989 = 15013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24989) = 3 ^ 9 * m + 15013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24989.1, data_15_24989.2]

/-- Complete interval computation for depth 15, residue 24990. -/
theorem bounds_15_24990 : exactInterval 15 24990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24990 : oddCount 24990 15 = 9 ∧ acceleratedOrbit 15 24990 = 15013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24990) = 3 ^ 9 * m + 15013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24990.1, data_15_24990.2]

/-- Complete interval computation for depth 15, residue 24991. -/
theorem bounds_15_24991 : exactInterval 15 24991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24991 : oddCount 24991 15 = 10 ∧ acceleratedOrbit 15 24991 = 45037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24991) = 3 ^ 10 * m + 45037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24991.1, data_15_24991.2]

/-- Complete interval computation for depth 15, residue 24992. -/
theorem bounds_15_24992 : exactInterval 15 24992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24992 : oddCount 24992 15 = 5 ∧ acceleratedOrbit 15 24992 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24992) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24992.1, data_15_24992.2]

/-- Complete interval computation for depth 15, residue 24993. -/
theorem bounds_15_24993 : exactInterval 15 24993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24993 : oddCount 24993 15 = 8 ∧ acceleratedOrbit 15 24993 = 5005 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24993) = 3 ^ 8 * m + 5005 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24993.1, data_15_24993.2]

/-- Complete interval computation for depth 15, residue 24994. -/
theorem bounds_15_24994 : exactInterval 15 24994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24994 : oddCount 24994 15 = 7 ∧ acceleratedOrbit 15 24994 = 1669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24994) = 3 ^ 7 * m + 1669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24994.1, data_15_24994.2]

/-- Complete interval computation for depth 15, residue 24995. -/
theorem bounds_15_24995 : exactInterval 15 24995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24995 : oddCount 24995 15 = 7 ∧ acceleratedOrbit 15 24995 = 1669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24995) = 3 ^ 7 * m + 1669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24995.1, data_15_24995.2]

/-- Complete interval computation for depth 15, residue 24996. -/
theorem bounds_15_24996 : exactInterval 15 24996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24996 : oddCount 24996 15 = 7 ∧ acceleratedOrbit 15 24996 = 1669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24996) = 3 ^ 7 * m + 1669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24996.1, data_15_24996.2]

/-- Complete interval computation for depth 15, residue 24997. -/
theorem bounds_15_24997 : exactInterval 15 24997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24997 : oddCount 24997 15 = 7 ∧ acceleratedOrbit 15 24997 = 1669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24997) = 3 ^ 7 * m + 1669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24997.1, data_15_24997.2]

/-- Complete interval computation for depth 15, residue 24998. -/
theorem bounds_15_24998 : exactInterval 15 24998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24998 : oddCount 24998 15 = 7 ∧ acceleratedOrbit 15 24998 = 1669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24998) = 3 ^ 7 * m + 1669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24998.1, data_15_24998.2]

/-- Complete interval computation for depth 15, residue 24999. -/
theorem bounds_15_24999 : exactInterval 15 24999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24999 : oddCount 24999 15 = 8 ∧ acceleratedOrbit 15 24999 = 5006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24999) = 3 ^ 8 * m + 5006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24999.1, data_15_24999.2]

/-- Complete interval computation for depth 15, residue 25000. -/
theorem bounds_15_25000 : exactInterval 15 25000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25000 : oddCount 25000 15 = 5 ∧ acceleratedOrbit 15 25000 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25000) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25000.1, data_15_25000.2]

end Collatz.Research.PassageAtlas.Batch0763
