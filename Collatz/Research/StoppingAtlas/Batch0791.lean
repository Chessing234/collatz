import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0791

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4966. -/
theorem bounds_13_4966 : exactInterval 13 4966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4966 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4966) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4966 : oddCount 4966 13 = 5 ∧ acceleratedOrbit 13 4966 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4966 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4966) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4966.1, data_13_4966.2]

/-- Complete interval computation for depth 13, residue 4967. -/
theorem bounds_13_4967 : exactInterval 13 4967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4967 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4967) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4967 : oddCount 4967 13 = 10 ∧ acceleratedOrbit 13 4967 = 35812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4967 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4967) = 3 ^ 10 * m + 35812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4967.1, data_13_4967.2]

/-- Complete interval computation for depth 13, residue 4968. -/
theorem bounds_13_4968 : exactInterval 13 4968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4968 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4968) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4968 : oddCount 4968 13 = 6 ∧ acceleratedOrbit 13 4968 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4968 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4968) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4968.1, data_13_4968.2]

/-- Complete interval computation for depth 13, residue 4969. -/
theorem bounds_13_4969 : exactInterval 13 4969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4969 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4969) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4969 : oddCount 4969 13 = 8 ∧ acceleratedOrbit 13 4969 = 3982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4969 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4969) = 3 ^ 8 * m + 3982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4969.1, data_13_4969.2]

/-- Complete interval computation for depth 13, residue 4970. -/
theorem bounds_13_4970 : exactInterval 13 4970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4970 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4970) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4970 : oddCount 4970 13 = 6 ∧ acceleratedOrbit 13 4970 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4970 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4970) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4970.1, data_13_4970.2]

/-- Complete interval computation for depth 13, residue 4971. -/
theorem bounds_13_4971 : exactInterval 13 4971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4971 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4971) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4971 : oddCount 4971 13 = 6 ∧ acceleratedOrbit 13 4971 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4971 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4971) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4971.1, data_13_4971.2]

/-- Complete interval computation for depth 13, residue 4972. -/
theorem bounds_13_4972 : exactInterval 13 4972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4972 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4972) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4972 : oddCount 4972 13 = 6 ∧ acceleratedOrbit 13 4972 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4972 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4972) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4972.1, data_13_4972.2]

/-- Complete interval computation for depth 13, residue 4973. -/
theorem bounds_13_4973 : exactInterval 13 4973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4973 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4973) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4973 : oddCount 4973 13 = 6 ∧ acceleratedOrbit 13 4973 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4973 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4973) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4973.1, data_13_4973.2]

/-- Complete interval computation for depth 13, residue 4974. -/
theorem bounds_13_4974 : exactInterval 13 4974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4974 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4974) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4974 : oddCount 4974 13 = 6 ∧ acceleratedOrbit 13 4974 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4974 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4974) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4974.1, data_13_4974.2]

/-- Complete interval computation for depth 13, residue 4975. -/
theorem bounds_13_4975 : exactInterval 13 4975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4975 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4975) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4975 : oddCount 4975 13 = 8 ∧ acceleratedOrbit 13 4975 = 3986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4975 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4975) = 3 ^ 8 * m + 3986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4975.1, data_13_4975.2]

/-- Complete interval computation for depth 13, residue 4976. -/
theorem bounds_13_4976 : exactInterval 13 4976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4976 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4976) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4976 : oddCount 4976 13 = 6 ∧ acceleratedOrbit 13 4976 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4976 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4976) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4976.1, data_13_4976.2]

/-- Complete interval computation for depth 13, residue 4977. -/
theorem bounds_13_4977 : exactInterval 13 4977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4977 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4977) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4977 : oddCount 4977 13 = 6 ∧ acceleratedOrbit 13 4977 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4977 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4977) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4977.1, data_13_4977.2]

/-- Complete interval computation for depth 13, residue 4978. -/
theorem bounds_13_4978 : exactInterval 13 4978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4978 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4978) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4978 : oddCount 4978 13 = 5 ∧ acceleratedOrbit 13 4978 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4978 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4978) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4978.1, data_13_4978.2]

/-- Complete interval computation for depth 13, residue 4979. -/
theorem bounds_13_4979 : exactInterval 13 4979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4979 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4979) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4979 : oddCount 4979 13 = 5 ∧ acceleratedOrbit 13 4979 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4979 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4979) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4979.1, data_13_4979.2]

/-- Complete interval computation for depth 13, residue 4980. -/
theorem bounds_13_4980 : exactInterval 13 4980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4980 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4980) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4980 : oddCount 4980 13 = 6 ∧ acceleratedOrbit 13 4980 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4980 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4980) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4980.1, data_13_4980.2]

end Collatz.Research.StoppingAtlas.Batch0791
