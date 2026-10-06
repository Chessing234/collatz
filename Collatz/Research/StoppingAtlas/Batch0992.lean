import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0992

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 8053. -/
theorem bounds_13_8053 : exactInterval 13 8053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8053 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8053) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8053 : oddCount 8053 13 = 6 ∧ acceleratedOrbit 13 8053 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8053 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8053) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8053.1, data_13_8053.2]

/-- Complete interval computation for depth 13, residue 8054. -/
theorem bounds_13_8054 : exactInterval 13 8054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8054 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8054) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8054 : oddCount 8054 13 = 5 ∧ acceleratedOrbit 13 8054 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8054 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8054) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8054.1, data_13_8054.2]

/-- Complete interval computation for depth 13, residue 8055. -/
theorem bounds_13_8055 : exactInterval 13 8055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8055 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8055) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8055 : oddCount 8055 13 = 5 ∧ acceleratedOrbit 13 8055 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8055 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8055) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8055.1, data_13_8055.2]

/-- Complete interval computation for depth 13, residue 8056. -/
theorem bounds_13_8056 : exactInterval 13 8056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8056 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8056) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8056 : oddCount 8056 13 = 7 ∧ acceleratedOrbit 13 8056 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8056 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8056) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8056.1, data_13_8056.2]

/-- Complete interval computation for depth 13, residue 8057. -/
theorem bounds_13_8057 : exactInterval 13 8057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8057 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8057) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8057 : oddCount 8057 13 = 8 ∧ acceleratedOrbit 13 8057 = 6455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8057 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8057) = 3 ^ 8 * m + 6455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8057.1, data_13_8057.2]

/-- Complete interval computation for depth 13, residue 8058. -/
theorem bounds_13_8058 : exactInterval 13 8058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8058 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8058) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8058 : oddCount 8058 13 = 7 ∧ acceleratedOrbit 13 8058 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8058 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8058) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8058.1, data_13_8058.2]

/-- Complete interval computation for depth 13, residue 8059. -/
theorem bounds_13_8059 : exactInterval 13 8059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8059 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8059) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8059 : oddCount 8059 13 = 7 ∧ acceleratedOrbit 13 8059 = 2152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8059 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8059) = 3 ^ 7 * m + 2152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8059.1, data_13_8059.2]

/-- Complete interval computation for depth 13, residue 8060. -/
theorem bounds_13_8060 : exactInterval 13 8060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8060 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8060) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8060 : oddCount 8060 13 = 7 ∧ acceleratedOrbit 13 8060 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8060 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8060) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8060.1, data_13_8060.2]

/-- Complete interval computation for depth 13, residue 8061. -/
theorem bounds_13_8061 : exactInterval 13 8061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8061 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8061) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8061 : oddCount 8061 13 = 7 ∧ acceleratedOrbit 13 8061 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8061 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8061) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8061.1, data_13_8061.2]

/-- Complete interval computation for depth 13, residue 8062. -/
theorem bounds_13_8062 : exactInterval 13 8062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8062 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8062) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8062 : oddCount 8062 13 = 9 ∧ acceleratedOrbit 13 8062 = 19376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8062 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8062) = 3 ^ 9 * m + 19376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8062.1, data_13_8062.2]

/-- Complete interval computation for depth 13, residue 8063. -/
theorem bounds_13_8063 : exactInterval 13 8063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8063 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8063) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8063 : oddCount 8063 13 = 9 ∧ acceleratedOrbit 13 8063 = 19376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8063 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8063) = 3 ^ 9 * m + 19376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8063.1, data_13_8063.2]

/-- Complete interval computation for depth 13, residue 8064. -/
theorem bounds_13_8064 : exactInterval 13 8064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8064 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8064) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8064 : oddCount 8064 13 = 6 ∧ acceleratedOrbit 13 8064 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8064 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8064) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8064.1, data_13_8064.2]

/-- Complete interval computation for depth 13, residue 8065. -/
theorem bounds_13_8065 : exactInterval 13 8065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8065 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8065) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8065 : oddCount 8065 13 = 6 ∧ acceleratedOrbit 13 8065 = 718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8065 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8065) = 3 ^ 6 * m + 718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8065.1, data_13_8065.2]

/-- Complete interval computation for depth 13, residue 8066. -/
theorem bounds_13_8066 : exactInterval 13 8066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8066 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8066) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8066 : oddCount 8066 13 = 6 ∧ acceleratedOrbit 13 8066 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8066 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8066) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8066.1, data_13_8066.2]

/-- Complete interval computation for depth 13, residue 8067. -/
theorem bounds_13_8067 : exactInterval 13 8067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8067 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8067) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8067 : oddCount 8067 13 = 6 ∧ acceleratedOrbit 13 8067 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8067 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8067) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8067.1, data_13_8067.2]

/-- Complete interval computation for depth 13, residue 8068. -/
theorem bounds_13_8068 : exactInterval 13 8068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8068 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8068) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8068 : oddCount 8068 13 = 8 ∧ acceleratedOrbit 13 8068 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8068 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8068) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8068.1, data_13_8068.2]

end Collatz.Research.StoppingAtlas.Batch0992
