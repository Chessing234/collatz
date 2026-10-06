import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0460

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3978. -/
theorem bounds_12_3978 : exactInterval 12 3978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3978 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3978) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3978 : oddCount 3978 12 = 4 ∧ acceleratedOrbit 12 3978 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3978 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3978) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3978.1, data_12_3978.2]

/-- Complete interval computation for depth 12, residue 3979. -/
theorem bounds_12_3979 : exactInterval 12 3979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3979 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3979) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3979 : oddCount 3979 12 = 7 ∧ acceleratedOrbit 12 3979 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3979 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3979) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3979.1, data_12_3979.2]

/-- Complete interval computation for depth 12, residue 3980. -/
theorem bounds_12_3980 : exactInterval 12 3980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3980 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3980) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3980 : oddCount 3980 12 = 4 ∧ acceleratedOrbit 12 3980 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3980 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3980) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3980.1, data_12_3980.2]

/-- Complete interval computation for depth 12, residue 3981. -/
theorem bounds_12_3981 : exactInterval 12 3981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3981 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3981) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3981 : oddCount 3981 12 = 4 ∧ acceleratedOrbit 12 3981 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3981 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3981) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3981.1, data_12_3981.2]

/-- Complete interval computation for depth 12, residue 3982. -/
theorem bounds_12_3982 : exactInterval 12 3982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3982 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3982) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3982 : oddCount 3982 12 = 7 ∧ acceleratedOrbit 12 3982 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3982 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3982) = 3 ^ 7 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3982.1, data_12_3982.2]

/-- Complete interval computation for depth 12, residue 3983. -/
theorem bounds_12_3983 : exactInterval 12 3983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3983 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3983) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3983 : oddCount 3983 12 = 7 ∧ acceleratedOrbit 12 3983 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3983 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3983) = 3 ^ 7 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3983.1, data_12_3983.2]

/-- Complete interval computation for depth 12, residue 3984. -/
theorem bounds_12_3984 : exactInterval 12 3984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3984 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3984) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3984 : oddCount 3984 12 = 5 ∧ acceleratedOrbit 12 3984 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3984 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3984) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3984.1, data_12_3984.2]

/-- Complete interval computation for depth 12, residue 3985. -/
theorem bounds_12_3985 : exactInterval 12 3985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3985 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3985) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3985 : oddCount 3985 12 = 7 ∧ acceleratedOrbit 12 3985 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3985 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3985) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3985.1, data_12_3985.2]

/-- Complete interval computation for depth 12, residue 3986. -/
theorem bounds_12_3986 : exactInterval 12 3986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3986 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3986) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3986 : oddCount 3986 12 = 7 ∧ acceleratedOrbit 12 3986 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3986 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3986) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3986.1, data_12_3986.2]

/-- Complete interval computation for depth 12, residue 3987. -/
theorem bounds_12_3987 : exactInterval 12 3987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3987 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3987) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3987 : oddCount 3987 12 = 7 ∧ acceleratedOrbit 12 3987 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3987 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3987) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3987.1, data_12_3987.2]

/-- Complete interval computation for depth 12, residue 3988. -/
theorem bounds_12_3988 : exactInterval 12 3988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3988 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3988) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3988 : oddCount 3988 12 = 5 ∧ acceleratedOrbit 12 3988 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3988 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3988) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3988.1, data_12_3988.2]

/-- Complete interval computation for depth 12, residue 3989. -/
theorem bounds_12_3989 : exactInterval 12 3989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3989 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3989) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3989 : oddCount 3989 12 = 5 ∧ acceleratedOrbit 12 3989 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3989 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3989) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3989.1, data_12_3989.2]

/-- Complete interval computation for depth 12, residue 3990. -/
theorem bounds_12_3990 : exactInterval 12 3990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3990 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3990) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3990 : oddCount 3990 12 = 4 ∧ acceleratedOrbit 12 3990 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3990 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3990) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3990.1, data_12_3990.2]

/-- Complete interval computation for depth 12, residue 3991. -/
theorem bounds_12_3991 : exactInterval 12 3991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3991 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3991) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3991 : oddCount 3991 12 = 4 ∧ acceleratedOrbit 12 3991 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3991 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3991) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3991.1, data_12_3991.2]

/-- Complete interval computation for depth 12, residue 3992. -/
theorem bounds_12_3992 : exactInterval 12 3992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3992 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3992) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3992 : oddCount 3992 12 = 5 ∧ acceleratedOrbit 12 3992 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3992 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3992) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3992.1, data_12_3992.2]

end Collatz.Research.StoppingAtlas.Batch0460
