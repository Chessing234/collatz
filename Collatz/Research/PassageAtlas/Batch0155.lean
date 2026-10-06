import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0155

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5046. -/
theorem bounds_15_5046 : exactInterval 15 5046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5046 : oddCount 5046 15 = 8 ∧ acceleratedOrbit 15 5046 = 1012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5046) = 3 ^ 8 * m + 1012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5046.1, data_15_5046.2]

/-- Complete interval computation for depth 15, residue 5047. -/
theorem bounds_15_5047 : exactInterval 15 5047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5047 : oddCount 5047 15 = 8 ∧ acceleratedOrbit 15 5047 = 1012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5047) = 3 ^ 8 * m + 1012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5047.1, data_15_5047.2]

/-- Complete interval computation for depth 15, residue 5048. -/
theorem bounds_15_5048 : exactInterval 15 5048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5048 : oddCount 5048 15 = 5 ∧ acceleratedOrbit 15 5048 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5048) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5048.1, data_15_5048.2]

/-- Complete interval computation for depth 15, residue 5049. -/
theorem bounds_15_5049 : exactInterval 15 5049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5049 : oddCount 5049 15 = 9 ∧ acceleratedOrbit 15 5049 = 3037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5049) = 3 ^ 9 * m + 3037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5049.1, data_15_5049.2]

/-- Complete interval computation for depth 15, residue 5050. -/
theorem bounds_15_5050 : exactInterval 15 5050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5050 : oddCount 5050 15 = 5 ∧ acceleratedOrbit 15 5050 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5050) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5050.1, data_15_5050.2]

/-- Complete interval computation for depth 15, residue 5051. -/
theorem bounds_15_5051 : exactInterval 15 5051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5051 : oddCount 5051 15 = 9 ∧ acceleratedOrbit 15 5051 = 3037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5051) = 3 ^ 9 * m + 3037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5051.1, data_15_5051.2]

/-- Complete interval computation for depth 15, residue 5052. -/
theorem bounds_15_5052 : exactInterval 15 5052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5052 : oddCount 5052 15 = 11 ∧ acceleratedOrbit 15 5052 = 27337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5052) = 3 ^ 11 * m + 27337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5052.1, data_15_5052.2]

/-- Complete interval computation for depth 15, residue 5053. -/
theorem bounds_15_5053 : exactInterval 15 5053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5053 : oddCount 5053 15 = 11 ∧ acceleratedOrbit 15 5053 = 27337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5053) = 3 ^ 11 * m + 27337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5053.1, data_15_5053.2]

/-- Complete interval computation for depth 15, residue 5054. -/
theorem bounds_15_5054 : exactInterval 15 5054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5054 : oddCount 5054 15 = 11 ∧ acceleratedOrbit 15 5054 = 27337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5054) = 3 ^ 11 * m + 27337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5054.1, data_15_5054.2]

/-- Complete interval computation for depth 15, residue 5055. -/
theorem bounds_15_5055 : exactInterval 15 5055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5055 : oddCount 5055 15 = 11 ∧ acceleratedOrbit 15 5055 = 27334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5055) = 3 ^ 11 * m + 27334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5055.1, data_15_5055.2]

/-- Complete interval computation for depth 15, residue 5056. -/
theorem bounds_15_5056 : exactInterval 15 5056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5056 : oddCount 5056 15 = 5 ∧ acceleratedOrbit 15 5056 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5056) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5056.1, data_15_5056.2]

/-- Complete interval computation for depth 15, residue 5057. -/
theorem bounds_15_5057 : exactInterval 15 5057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5057 : oddCount 5057 15 = 7 ∧ acceleratedOrbit 15 5057 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5057) = 3 ^ 7 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5057.1, data_15_5057.2]

/-- Complete interval computation for depth 15, residue 5058. -/
theorem bounds_15_5058 : exactInterval 15 5058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5058 : oddCount 5058 15 = 7 ∧ acceleratedOrbit 15 5058 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5058) = 3 ^ 7 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5058.1, data_15_5058.2]

/-- Complete interval computation for depth 15, residue 5059. -/
theorem bounds_15_5059 : exactInterval 15 5059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5059 : oddCount 5059 15 = 7 ∧ acceleratedOrbit 15 5059 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5059) = 3 ^ 7 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5059.1, data_15_5059.2]

/-- Complete interval computation for depth 15, residue 5060. -/
theorem bounds_15_5060 : exactInterval 15 5060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5060 : oddCount 5060 15 = 5 ∧ acceleratedOrbit 15 5060 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5060) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5060.1, data_15_5060.2]

/-- Complete interval computation for depth 15, residue 5061. -/
theorem bounds_15_5061 : exactInterval 15 5061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5061 : oddCount 5061 15 = 5 ∧ acceleratedOrbit 15 5061 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5061) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5061.1, data_15_5061.2]

/-- Complete interval computation for depth 15, residue 5062. -/
theorem bounds_15_5062 : exactInterval 15 5062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5062 : oddCount 5062 15 = 5 ∧ acceleratedOrbit 15 5062 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5062) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5062.1, data_15_5062.2]

/-- Complete interval computation for depth 15, residue 5063. -/
theorem bounds_15_5063 : exactInterval 15 5063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5063 : oddCount 5063 15 = 10 ∧ acceleratedOrbit 15 5063 = 9128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5063) = 3 ^ 10 * m + 9128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5063.1, data_15_5063.2]

/-- Complete interval computation for depth 15, residue 5064. -/
theorem bounds_15_5064 : exactInterval 15 5064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5064 : oddCount 5064 15 = 6 ∧ acceleratedOrbit 15 5064 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5064) = 3 ^ 6 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5064.1, data_15_5064.2]

/-- Complete interval computation for depth 15, residue 5065. -/
theorem bounds_15_5065 : exactInterval 15 5065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5065 : oddCount 5065 15 = 8 ∧ acceleratedOrbit 15 5065 = 1016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5065) = 3 ^ 8 * m + 1016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5065.1, data_15_5065.2]

/-- Complete interval computation for depth 15, residue 5066. -/
theorem bounds_15_5066 : exactInterval 15 5066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5066 : oddCount 5066 15 = 6 ∧ acceleratedOrbit 15 5066 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5066) = 3 ^ 6 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5066.1, data_15_5066.2]

/-- Complete interval computation for depth 15, residue 5067. -/
theorem bounds_15_5067 : exactInterval 15 5067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5067 : oddCount 5067 15 = 6 ∧ acceleratedOrbit 15 5067 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5067) = 3 ^ 6 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5067.1, data_15_5067.2]

/-- Complete interval computation for depth 15, residue 5068. -/
theorem bounds_15_5068 : exactInterval 15 5068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5068 : oddCount 5068 15 = 6 ∧ acceleratedOrbit 15 5068 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5068) = 3 ^ 6 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5068.1, data_15_5068.2]

/-- Complete interval computation for depth 15, residue 5069. -/
theorem bounds_15_5069 : exactInterval 15 5069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5069 : oddCount 5069 15 = 6 ∧ acceleratedOrbit 15 5069 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5069) = 3 ^ 6 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5069.1, data_15_5069.2]

/-- Complete interval computation for depth 15, residue 5070. -/
theorem bounds_15_5070 : exactInterval 15 5070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5070 : oddCount 5070 15 = 10 ∧ acceleratedOrbit 15 5070 = 9143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5070) = 3 ^ 10 * m + 9143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5070.1, data_15_5070.2]

/-- Complete interval computation for depth 15, residue 5071. -/
theorem bounds_15_5071 : exactInterval 15 5071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5071 : oddCount 5071 15 = 10 ∧ acceleratedOrbit 15 5071 = 9143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5071) = 3 ^ 10 * m + 9143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5071.1, data_15_5071.2]

/-- Complete interval computation for depth 15, residue 5072. -/
theorem bounds_15_5072 : exactInterval 15 5072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5072 : oddCount 5072 15 = 5 ∧ acceleratedOrbit 15 5072 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5072) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5072.1, data_15_5072.2]

/-- Complete interval computation for depth 15, residue 5073. -/
theorem bounds_15_5073 : exactInterval 15 5073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5073 : oddCount 5073 15 = 6 ∧ acceleratedOrbit 15 5073 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5073) = 3 ^ 6 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5073.1, data_15_5073.2]

/-- Complete interval computation for depth 15, residue 5074. -/
theorem bounds_15_5074 : exactInterval 15 5074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5074 : oddCount 5074 15 = 10 ∧ acceleratedOrbit 15 5074 = 9152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5074) = 3 ^ 10 * m + 9152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5074.1, data_15_5074.2]

/-- Complete interval computation for depth 15, residue 5075. -/
theorem bounds_15_5075 : exactInterval 15 5075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5075 : oddCount 5075 15 = 10 ∧ acceleratedOrbit 15 5075 = 9152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5075) = 3 ^ 10 * m + 9152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5075.1, data_15_5075.2]

/-- Complete interval computation for depth 15, residue 5076. -/
theorem bounds_15_5076 : exactInterval 15 5076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5076 : oddCount 5076 15 = 5 ∧ acceleratedOrbit 15 5076 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5076) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5076.1, data_15_5076.2]

/-- Complete interval computation for depth 15, residue 5077. -/
theorem bounds_15_5077 : exactInterval 15 5077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5077 : oddCount 5077 15 = 5 ∧ acceleratedOrbit 15 5077 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5077) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5077.1, data_15_5077.2]

/-- Complete interval computation for depth 15, residue 5078. -/
theorem bounds_15_5078 : exactInterval 15 5078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5078 : oddCount 5078 15 = 9 ∧ acceleratedOrbit 15 5078 = 3053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5078) = 3 ^ 9 * m + 3053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5078.1, data_15_5078.2]

end Collatz.Research.PassageAtlas.Batch0155
