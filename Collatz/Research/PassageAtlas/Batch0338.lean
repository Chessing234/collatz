import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0338

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11042. -/
theorem bounds_15_11042 : exactInterval 15 11042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11042 : oddCount 11042 15 = 5 ∧ acceleratedOrbit 15 11042 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11042) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11042.1, data_15_11042.2]

/-- Complete interval computation for depth 15, residue 11043. -/
theorem bounds_15_11043 : exactInterval 15 11043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11043 : oddCount 11043 15 = 5 ∧ acceleratedOrbit 15 11043 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11043) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11043.1, data_15_11043.2]

/-- Complete interval computation for depth 15, residue 11044. -/
theorem bounds_15_11044 : exactInterval 15 11044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11044 : oddCount 11044 15 = 5 ∧ acceleratedOrbit 15 11044 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11044) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11044.1, data_15_11044.2]

/-- Complete interval computation for depth 15, residue 11045. -/
theorem bounds_15_11045 : exactInterval 15 11045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11045 : oddCount 11045 15 = 5 ∧ acceleratedOrbit 15 11045 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11045) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11045.1, data_15_11045.2]

/-- Complete interval computation for depth 15, residue 11046. -/
theorem bounds_15_11046 : exactInterval 15 11046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11046 : oddCount 11046 15 = 5 ∧ acceleratedOrbit 15 11046 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11046) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11046.1, data_15_11046.2]

/-- Complete interval computation for depth 15, residue 11047. -/
theorem bounds_15_11047 : exactInterval 15 11047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11047 : oddCount 11047 15 = 9 ∧ acceleratedOrbit 15 11047 = 6637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11047) = 3 ^ 9 * m + 6637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11047.1, data_15_11047.2]

/-- Complete interval computation for depth 15, residue 11048. -/
theorem bounds_15_11048 : exactInterval 15 11048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11048 : oddCount 11048 15 = 5 ∧ acceleratedOrbit 15 11048 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11048) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11048.1, data_15_11048.2]

/-- Complete interval computation for depth 15, residue 11049. -/
theorem bounds_15_11049 : exactInterval 15 11049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11049 : oddCount 11049 15 = 10 ∧ acceleratedOrbit 15 11049 = 19916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11049) = 3 ^ 10 * m + 19916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11049.1, data_15_11049.2]

/-- Complete interval computation for depth 15, residue 11050. -/
theorem bounds_15_11050 : exactInterval 15 11050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11050 : oddCount 11050 15 = 5 ∧ acceleratedOrbit 15 11050 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11050) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11050.1, data_15_11050.2]

/-- Complete interval computation for depth 15, residue 11051. -/
theorem bounds_15_11051 : exactInterval 15 11051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11051 : oddCount 11051 15 = 10 ∧ acceleratedOrbit 15 11051 = 19925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11051) = 3 ^ 10 * m + 19925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11051.1, data_15_11051.2]

/-- Complete interval computation for depth 15, residue 11052. -/
theorem bounds_15_11052 : exactInterval 15 11052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11052 : oddCount 11052 15 = 7 ∧ acceleratedOrbit 15 11052 = 739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11052) = 3 ^ 7 * m + 739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11052.1, data_15_11052.2]

/-- Complete interval computation for depth 15, residue 11053. -/
theorem bounds_15_11053 : exactInterval 15 11053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11053 : oddCount 11053 15 = 7 ∧ acceleratedOrbit 15 11053 = 739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11053) = 3 ^ 7 * m + 739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11053.1, data_15_11053.2]

/-- Complete interval computation for depth 15, residue 11054. -/
theorem bounds_15_11054 : exactInterval 15 11054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11054 : oddCount 11054 15 = 7 ∧ acceleratedOrbit 15 11054 = 739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11054) = 3 ^ 7 * m + 739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11054.1, data_15_11054.2]

/-- Complete interval computation for depth 15, residue 11055. -/
theorem bounds_15_11055 : exactInterval 15 11055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11055 : oddCount 11055 15 = 11 ∧ acceleratedOrbit 15 11055 = 59777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11055) = 3 ^ 11 * m + 59777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11055.1, data_15_11055.2]

/-- Complete interval computation for depth 15, residue 11056. -/
theorem bounds_15_11056 : exactInterval 15 11056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11056 : oddCount 11056 15 = 5 ∧ acceleratedOrbit 15 11056 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11056) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11056.1, data_15_11056.2]

/-- Complete interval computation for depth 15, residue 11057. -/
theorem bounds_15_11057 : exactInterval 15 11057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11057 : oddCount 11057 15 = 7 ∧ acceleratedOrbit 15 11057 = 739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11057) = 3 ^ 7 * m + 739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11057.1, data_15_11057.2]

/-- Complete interval computation for depth 15, residue 11058. -/
theorem bounds_15_11058 : exactInterval 15 11058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11058 : oddCount 11058 15 = 7 ∧ acceleratedOrbit 15 11058 = 739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11058) = 3 ^ 7 * m + 739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11058.1, data_15_11058.2]

/-- Complete interval computation for depth 15, residue 11059. -/
theorem bounds_15_11059 : exactInterval 15 11059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11059 : oddCount 11059 15 = 7 ∧ acceleratedOrbit 15 11059 = 739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11059) = 3 ^ 7 * m + 739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11059.1, data_15_11059.2]

/-- Complete interval computation for depth 15, residue 11060. -/
theorem bounds_15_11060 : exactInterval 15 11060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11060 : oddCount 11060 15 = 5 ∧ acceleratedOrbit 15 11060 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11060) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11060.1, data_15_11060.2]

/-- Complete interval computation for depth 15, residue 11061. -/
theorem bounds_15_11061 : exactInterval 15 11061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11061 : oddCount 11061 15 = 5 ∧ acceleratedOrbit 15 11061 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11061) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11061.1, data_15_11061.2]

/-- Complete interval computation for depth 15, residue 11062. -/
theorem bounds_15_11062 : exactInterval 15 11062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11062 : oddCount 11062 15 = 8 ∧ acceleratedOrbit 15 11062 = 2216 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11062) = 3 ^ 8 * m + 2216 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11062.1, data_15_11062.2]

/-- Complete interval computation for depth 15, residue 11063. -/
theorem bounds_15_11063 : exactInterval 15 11063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11063 : oddCount 11063 15 = 8 ∧ acceleratedOrbit 15 11063 = 2216 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11063) = 3 ^ 8 * m + 2216 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11063.1, data_15_11063.2]

/-- Complete interval computation for depth 15, residue 11064. -/
theorem bounds_15_11064 : exactInterval 15 11064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11064 : oddCount 11064 15 = 9 ∧ acceleratedOrbit 15 11064 = 6652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11064) = 3 ^ 9 * m + 6652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11064.1, data_15_11064.2]

/-- Complete interval computation for depth 15, residue 11065. -/
theorem bounds_15_11065 : exactInterval 15 11065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11065 : oddCount 11065 15 = 10 ∧ acceleratedOrbit 15 11065 = 19946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11065) = 3 ^ 10 * m + 19946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11065.1, data_15_11065.2]

/-- Complete interval computation for depth 15, residue 11066. -/
theorem bounds_15_11066 : exactInterval 15 11066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11066 : oddCount 11066 15 = 9 ∧ acceleratedOrbit 15 11066 = 6652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11066) = 3 ^ 9 * m + 6652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11066.1, data_15_11066.2]

/-- Complete interval computation for depth 15, residue 11067. -/
theorem bounds_15_11067 : exactInterval 15 11067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11067 : oddCount 11067 15 = 7 ∧ acceleratedOrbit 15 11067 = 739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11067) = 3 ^ 7 * m + 739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11067.1, data_15_11067.2]

/-- Complete interval computation for depth 15, residue 11068. -/
theorem bounds_15_11068 : exactInterval 15 11068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11068 : oddCount 11068 15 = 9 ∧ acceleratedOrbit 15 11068 = 6652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11068) = 3 ^ 9 * m + 6652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11068.1, data_15_11068.2]

/-- Complete interval computation for depth 15, residue 11069. -/
theorem bounds_15_11069 : exactInterval 15 11069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11069 : oddCount 11069 15 = 9 ∧ acceleratedOrbit 15 11069 = 6652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11069) = 3 ^ 9 * m + 6652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11069.1, data_15_11069.2]

/-- Complete interval computation for depth 15, residue 11070. -/
theorem bounds_15_11070 : exactInterval 15 11070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11070 : oddCount 11070 15 = 12 ∧ acceleratedOrbit 15 11070 = 179576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11070) = 3 ^ 12 * m + 179576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11070.1, data_15_11070.2]

/-- Complete interval computation for depth 15, residue 11071. -/
theorem bounds_15_11071 : exactInterval 15 11071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11071 : oddCount 11071 15 = 12 ∧ acceleratedOrbit 15 11071 = 179576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11071) = 3 ^ 12 * m + 179576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11071.1, data_15_11071.2]

/-- Complete interval computation for depth 15, residue 11072. -/
theorem bounds_15_11072 : exactInterval 15 11072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11072 : oddCount 11072 15 = 4 ∧ acceleratedOrbit 15 11072 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11072) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11072.1, data_15_11072.2]

/-- Complete interval computation for depth 15, residue 11073. -/
theorem bounds_15_11073 : exactInterval 15 11073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11073 : oddCount 11073 15 = 5 ∧ acceleratedOrbit 15 11073 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11073) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11073.1, data_15_11073.2]

/-- Complete interval computation for depth 15, residue 11074. -/
theorem bounds_15_11074 : exactInterval 15 11074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11074 : oddCount 11074 15 = 7 ∧ acceleratedOrbit 15 11074 = 740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11074) = 3 ^ 7 * m + 740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11074.1, data_15_11074.2]

end Collatz.Research.PassageAtlas.Batch0338
