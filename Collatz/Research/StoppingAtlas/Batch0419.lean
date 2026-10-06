import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0419

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3348. -/
theorem bounds_12_3348 : exactInterval 12 3348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3348 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3348) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3348 : oddCount 3348 12 = 4 ∧ acceleratedOrbit 12 3348 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3348 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3348) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3348.1, data_12_3348.2]

/-- Complete interval computation for depth 12, residue 3349. -/
theorem bounds_12_3349 : exactInterval 12 3349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3349 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3349) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3349 : oddCount 3349 12 = 4 ∧ acceleratedOrbit 12 3349 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3349 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3349) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3349.1, data_12_3349.2]

/-- Complete interval computation for depth 12, residue 3350. -/
theorem bounds_12_3350 : exactInterval 12 3350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3350 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3350) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3350 : oddCount 3350 12 = 5 ∧ acceleratedOrbit 12 3350 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3350 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3350) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3350.1, data_12_3350.2]

/-- Complete interval computation for depth 12, residue 3351. -/
theorem bounds_12_3351 : exactInterval 12 3351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3351 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3351) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3351 : oddCount 3351 12 = 5 ∧ acceleratedOrbit 12 3351 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3351 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3351) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3351.1, data_12_3351.2]

/-- Complete interval computation for depth 12, residue 3352. -/
theorem bounds_12_3352 : exactInterval 12 3352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3352 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3352) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3352 : oddCount 3352 12 = 4 ∧ acceleratedOrbit 12 3352 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3352 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3352) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3352.1, data_12_3352.2]

/-- Complete interval computation for depth 12, residue 3353. -/
theorem bounds_12_3353 : exactInterval 12 3353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3353 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3353) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3353 : oddCount 3353 12 = 7 ∧ acceleratedOrbit 12 3353 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3353 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3353) = 3 ^ 7 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3353.1, data_12_3353.2]

/-- Complete interval computation for depth 12, residue 3354. -/
theorem bounds_12_3354 : exactInterval 12 3354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3354 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3354) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3354 : oddCount 3354 12 = 4 ∧ acceleratedOrbit 12 3354 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3354 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3354) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3354.1, data_12_3354.2]

/-- Complete interval computation for depth 12, residue 3355. -/
theorem bounds_12_3355 : exactInterval 12 3355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3355 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3355) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3355 : oddCount 3355 12 = 9 ∧ acceleratedOrbit 12 3355 = 16129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3355 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3355) = 3 ^ 9 * m + 16129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3355.1, data_12_3355.2]

/-- Complete interval computation for depth 12, residue 3356. -/
theorem bounds_12_3356 : exactInterval 12 3356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3356 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3356) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3356 : oddCount 3356 12 = 7 ∧ acceleratedOrbit 12 3356 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3356 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3356) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3356.1, data_12_3356.2]

/-- Complete interval computation for depth 12, residue 3357. -/
theorem bounds_12_3357 : exactInterval 12 3357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3357 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3357) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3357 : oddCount 3357 12 = 7 ∧ acceleratedOrbit 12 3357 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3357 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3357) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3357.1, data_12_3357.2]

/-- Complete interval computation for depth 12, residue 3358. -/
theorem bounds_12_3358 : exactInterval 12 3358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3358 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3358) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3358 : oddCount 3358 12 = 7 ∧ acceleratedOrbit 12 3358 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3358 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3358) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3358.1, data_12_3358.2]

/-- Complete interval computation for depth 12, residue 3359. -/
theorem bounds_12_3359 : exactInterval 12 3359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3359 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3359) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3359 : oddCount 3359 12 = 6 ∧ acceleratedOrbit 12 3359 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3359 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3359) = 3 ^ 6 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3359.1, data_12_3359.2]

/-- Complete interval computation for depth 12, residue 3360. -/
theorem bounds_12_3360 : exactInterval 12 3360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3360 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3360) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3360 : oddCount 3360 12 = 5 ∧ acceleratedOrbit 12 3360 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3360 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3360) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3360.1, data_12_3360.2]

/-- Complete interval computation for depth 12, residue 3361. -/
theorem bounds_12_3361 : exactInterval 12 3361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3361 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3361) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3361 : oddCount 3361 12 = 5 ∧ acceleratedOrbit 12 3361 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3361 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3361) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3361.1, data_12_3361.2]

/-- Complete interval computation for depth 12, residue 3362. -/
theorem bounds_12_3362 : exactInterval 12 3362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3362 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3362) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3362 : oddCount 3362 12 = 5 ∧ acceleratedOrbit 12 3362 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3362 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3362) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3362.1, data_12_3362.2]

end Collatz.Research.StoppingAtlas.Batch0419
