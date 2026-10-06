import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0394

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2964. -/
theorem bounds_12_2964 : exactInterval 12 2964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2964 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2964) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2964 : oddCount 2964 12 = 4 ∧ acceleratedOrbit 12 2964 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2964 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2964) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2964.1, data_12_2964.2]

/-- Complete interval computation for depth 12, residue 2965. -/
theorem bounds_12_2965 : exactInterval 12 2965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2965 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2965) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2965 : oddCount 2965 12 = 4 ∧ acceleratedOrbit 12 2965 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2965 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2965) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2965.1, data_12_2965.2]

/-- Complete interval computation for depth 12, residue 2966. -/
theorem bounds_12_2966 : exactInterval 12 2966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2966 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2966) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2966 : oddCount 2966 12 = 6 ∧ acceleratedOrbit 12 2966 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2966 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2966) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2966.1, data_12_2966.2]

/-- Complete interval computation for depth 12, residue 2967. -/
theorem bounds_12_2967 : exactInterval 12 2967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2967 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2967) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2967 : oddCount 2967 12 = 6 ∧ acceleratedOrbit 12 2967 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2967 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2967) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2967.1, data_12_2967.2]

/-- Complete interval computation for depth 12, residue 2968. -/
theorem bounds_12_2968 : exactInterval 12 2968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2968 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2968) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2968 : oddCount 2968 12 = 4 ∧ acceleratedOrbit 12 2968 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2968 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2968) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2968.1, data_12_2968.2]

/-- Complete interval computation for depth 12, residue 2969. -/
theorem bounds_12_2969 : exactInterval 12 2969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2969 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2969) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2969 : oddCount 2969 12 = 6 ∧ acceleratedOrbit 12 2969 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2969 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2969) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2969.1, data_12_2969.2]

/-- Complete interval computation for depth 12, residue 2970. -/
theorem bounds_12_2970 : exactInterval 12 2970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2970 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2970) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2970 : oddCount 2970 12 = 4 ∧ acceleratedOrbit 12 2970 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2970 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2970) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2970.1, data_12_2970.2]

/-- Complete interval computation for depth 12, residue 2971. -/
theorem bounds_12_2971 : exactInterval 12 2971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2971 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2971) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2971 : oddCount 2971 12 = 6 ∧ acceleratedOrbit 12 2971 = 529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2971 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2971) = 3 ^ 6 * m + 529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2971.1, data_12_2971.2]

/-- Complete interval computation for depth 12, residue 2972. -/
theorem bounds_12_2972 : exactInterval 12 2972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2972 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2972) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2972 : oddCount 2972 12 = 8 ∧ acceleratedOrbit 12 2972 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2972 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2972) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2972.1, data_12_2972.2]

/-- Complete interval computation for depth 12, residue 2973. -/
theorem bounds_12_2973 : exactInterval 12 2973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2973 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2973) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2973 : oddCount 2973 12 = 8 ∧ acceleratedOrbit 12 2973 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2973 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2973) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2973.1, data_12_2973.2]

/-- Complete interval computation for depth 12, residue 2974. -/
theorem bounds_12_2974 : exactInterval 12 2974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2974 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2974) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2974 : oddCount 2974 12 = 8 ∧ acceleratedOrbit 12 2974 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2974 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2974) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2974.1, data_12_2974.2]

/-- Complete interval computation for depth 12, residue 2975. -/
theorem bounds_12_2975 : exactInterval 12 2975 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2975 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2975) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2975 : oddCount 2975 12 = 7 ∧ acceleratedOrbit 12 2975 = 1589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2975 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2975) = 3 ^ 7 * m + 1589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2975.1, data_12_2975.2]

/-- Complete interval computation for depth 12, residue 2976. -/
theorem bounds_12_2976 : exactInterval 12 2976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2976 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2976) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2976 : oddCount 2976 12 = 3 ∧ acceleratedOrbit 12 2976 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2976 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2976) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2976.1, data_12_2976.2]

/-- Complete interval computation for depth 12, residue 2977. -/
theorem bounds_12_2977 : exactInterval 12 2977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2977 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2977) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2977 : oddCount 2977 12 = 7 ∧ acceleratedOrbit 12 2977 = 1592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2977 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2977) = 3 ^ 7 * m + 1592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2977.1, data_12_2977.2]

/-- Complete interval computation for depth 12, residue 2978. -/
theorem bounds_12_2978 : exactInterval 12 2978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2978 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2978) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2978 : oddCount 2978 12 = 4 ∧ acceleratedOrbit 12 2978 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2978 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2978) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2978.1, data_12_2978.2]

end Collatz.Research.StoppingAtlas.Batch0394
