import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0682

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3292. -/
theorem bounds_13_3292 : exactInterval 13 3292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3292 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3292) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3292 : oddCount 3292 13 = 7 ∧ acceleratedOrbit 13 3292 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3292 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3292) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3292.1, data_13_3292.2]

/-- Complete interval computation for depth 13, residue 3293. -/
theorem bounds_13_3293 : exactInterval 13 3293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3293 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3293) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3293 : oddCount 3293 13 = 7 ∧ acceleratedOrbit 13 3293 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3293 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3293) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3293.1, data_13_3293.2]

/-- Complete interval computation for depth 13, residue 3294. -/
theorem bounds_13_3294 : exactInterval 13 3294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3294 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3294) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3294 : oddCount 3294 13 = 7 ∧ acceleratedOrbit 13 3294 = 880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3294 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3294) = 3 ^ 7 * m + 880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3294.1, data_13_3294.2]

/-- Complete interval computation for depth 13, residue 3295. -/
theorem bounds_13_3295 : exactInterval 13 3295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3295 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3295) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3295 : oddCount 3295 13 = 7 ∧ acceleratedOrbit 13 3295 = 880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3295 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3295) = 3 ^ 7 * m + 880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3295.1, data_13_3295.2]

/-- Complete interval computation for depth 13, residue 3296. -/
theorem bounds_13_3296 : exactInterval 13 3296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3296 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3296) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3296 : oddCount 3296 13 = 7 ∧ acceleratedOrbit 13 3296 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3296 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3296) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3296.1, data_13_3296.2]

/-- Complete interval computation for depth 13, residue 3297. -/
theorem bounds_13_3297 : exactInterval 13 3297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3297 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3297) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3297 : oddCount 3297 13 = 9 ∧ acceleratedOrbit 13 3297 = 7928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3297 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3297) = 3 ^ 9 * m + 7928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3297.1, data_13_3297.2]

/-- Complete interval computation for depth 13, residue 3298. -/
theorem bounds_13_3298 : exactInterval 13 3298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3298 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3298) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3298 : oddCount 3298 13 = 3 ∧ acceleratedOrbit 13 3298 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3298 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3298) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3298.1, data_13_3298.2]

/-- Complete interval computation for depth 13, residue 3299. -/
theorem bounds_13_3299 : exactInterval 13 3299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3299 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3299) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3299 : oddCount 3299 13 = 3 ∧ acceleratedOrbit 13 3299 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3299 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3299) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3299.1, data_13_3299.2]

/-- Complete interval computation for depth 13, residue 3300. -/
theorem bounds_13_3300 : exactInterval 13 3300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3300 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3300) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3300 : oddCount 3300 13 = 7 ∧ acceleratedOrbit 13 3300 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3300 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3300) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3300.1, data_13_3300.2]

/-- Complete interval computation for depth 13, residue 3301. -/
theorem bounds_13_3301 : exactInterval 13 3301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3301 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3301) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3301 : oddCount 3301 13 = 7 ∧ acceleratedOrbit 13 3301 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3301 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3301) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3301.1, data_13_3301.2]

/-- Complete interval computation for depth 13, residue 3302. -/
theorem bounds_13_3302 : exactInterval 13 3302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3302 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3302) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3302 : oddCount 3302 13 = 7 ∧ acceleratedOrbit 13 3302 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3302 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3302) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3302.1, data_13_3302.2]

/-- Complete interval computation for depth 13, residue 3303. -/
theorem bounds_13_3303 : exactInterval 13 3303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3303 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3303) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3303 : oddCount 3303 13 = 9 ∧ acceleratedOrbit 13 3303 = 7940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3303 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3303) = 3 ^ 9 * m + 7940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3303.1, data_13_3303.2]

/-- Complete interval computation for depth 13, residue 3304. -/
theorem bounds_13_3304 : exactInterval 13 3304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3304 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3304) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3304 : oddCount 3304 13 = 7 ∧ acceleratedOrbit 13 3304 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3304 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3304) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3304.1, data_13_3304.2]

/-- Complete interval computation for depth 13, residue 3305. -/
theorem bounds_13_3305 : exactInterval 13 3305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3305 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3305) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3305 : oddCount 3305 13 = 7 ∧ acceleratedOrbit 13 3305 = 883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3305 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3305) = 3 ^ 7 * m + 883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3305.1, data_13_3305.2]

/-- Complete interval computation for depth 13, residue 3306. -/
theorem bounds_13_3306 : exactInterval 13 3306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3306 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3306) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3306 : oddCount 3306 13 = 7 ∧ acceleratedOrbit 13 3306 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3306 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3306) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3306.1, data_13_3306.2]

end Collatz.Research.StoppingAtlas.Batch0682
