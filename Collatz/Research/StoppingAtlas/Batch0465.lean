import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0465

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 4055. -/
theorem bounds_12_4055 : exactInterval 12 4055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4055 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4055) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4055 : oddCount 4055 12 = 8 ∧ acceleratedOrbit 12 4055 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4055 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4055) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4055.1, data_12_4055.2]

/-- Complete interval computation for depth 12, residue 4056. -/
theorem bounds_12_4056 : exactInterval 12 4056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4056 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4056) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4056 : oddCount 4056 12 = 6 ∧ acceleratedOrbit 12 4056 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4056 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4056) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4056.1, data_12_4056.2]

/-- Complete interval computation for depth 12, residue 4057. -/
theorem bounds_12_4057 : exactInterval 12 4057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4057 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4057) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4057 : oddCount 4057 12 = 5 ∧ acceleratedOrbit 12 4057 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4057 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4057) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4057.1, data_12_4057.2]

/-- Complete interval computation for depth 12, residue 4058. -/
theorem bounds_12_4058 : exactInterval 12 4058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4058 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4058) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4058 : oddCount 4058 12 = 6 ∧ acceleratedOrbit 12 4058 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4058 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4058) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4058.1, data_12_4058.2]

/-- Complete interval computation for depth 12, residue 4059. -/
theorem bounds_12_4059 : exactInterval 12 4059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4059 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4059) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4059 : oddCount 4059 12 = 8 ∧ acceleratedOrbit 12 4059 = 6506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4059 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4059) = 3 ^ 8 * m + 6506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4059.1, data_12_4059.2]

/-- Complete interval computation for depth 12, residue 4060. -/
theorem bounds_12_4060 : exactInterval 12 4060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4060 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4060) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4060 : oddCount 4060 12 = 6 ∧ acceleratedOrbit 12 4060 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4060 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4060) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4060.1, data_12_4060.2]

/-- Complete interval computation for depth 12, residue 4061. -/
theorem bounds_12_4061 : exactInterval 12 4061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4061 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4061) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4061 : oddCount 4061 12 = 6 ∧ acceleratedOrbit 12 4061 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4061 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4061) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4061.1, data_12_4061.2]

/-- Complete interval computation for depth 12, residue 4062. -/
theorem bounds_12_4062 : exactInterval 12 4062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4062 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4062) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4062 : oddCount 4062 12 = 7 ∧ acceleratedOrbit 12 4062 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4062 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4062) = 3 ^ 7 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4062.1, data_12_4062.2]

/-- Complete interval computation for depth 12, residue 4063. -/
theorem bounds_12_4063 : exactInterval 12 4063 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4063 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4063) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4063 : oddCount 4063 12 = 7 ∧ acceleratedOrbit 12 4063 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4063 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4063) = 3 ^ 7 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4063.1, data_12_4063.2]

/-- Complete interval computation for depth 12, residue 4064. -/
theorem bounds_12_4064 : exactInterval 12 4064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4064 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4064) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4064 : oddCount 4064 12 = 7 ∧ acceleratedOrbit 12 4064 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4064 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4064) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4064.1, data_12_4064.2]

/-- Complete interval computation for depth 12, residue 4065. -/
theorem bounds_12_4065 : exactInterval 12 4065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4065 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4065) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4065 : oddCount 4065 12 = 9 ∧ acceleratedOrbit 12 4065 = 19547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4065 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4065) = 3 ^ 9 * m + 19547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4065.1, data_12_4065.2]

/-- Complete interval computation for depth 12, residue 4066. -/
theorem bounds_12_4066 : exactInterval 12 4066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4066 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4066) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4066 : oddCount 4066 12 = 6 ∧ acceleratedOrbit 12 4066 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4066 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4066) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4066.1, data_12_4066.2]

/-- Complete interval computation for depth 12, residue 4067. -/
theorem bounds_12_4067 : exactInterval 12 4067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4067 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4067) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4067 : oddCount 4067 12 = 6 ∧ acceleratedOrbit 12 4067 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4067 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4067) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4067.1, data_12_4067.2]

/-- Complete interval computation for depth 12, residue 4068. -/
theorem bounds_12_4068 : exactInterval 12 4068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4068 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4068) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4068 : oddCount 4068 12 = 7 ∧ acceleratedOrbit 12 4068 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4068 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4068) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4068.1, data_12_4068.2]

/-- Complete interval computation for depth 12, residue 4069. -/
theorem bounds_12_4069 : exactInterval 12 4069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4069 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4069) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4069 : oddCount 4069 12 = 7 ∧ acceleratedOrbit 12 4069 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4069 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4069) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4069.1, data_12_4069.2]

end Collatz.Research.StoppingAtlas.Batch0465
