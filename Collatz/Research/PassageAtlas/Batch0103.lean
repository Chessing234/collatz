import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0103

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3342. -/
theorem bounds_15_3342 : exactInterval 15 3342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3342 : oddCount 3342 15 = 7 ∧ acceleratedOrbit 15 3342 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3342) = 3 ^ 7 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3342.1, data_15_3342.2]

/-- Complete interval computation for depth 15, residue 3343. -/
theorem bounds_15_3343 : exactInterval 15 3343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3343 : oddCount 3343 15 = 7 ∧ acceleratedOrbit 15 3343 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3343) = 3 ^ 7 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3343.1, data_15_3343.2]

/-- Complete interval computation for depth 15, residue 3344. -/
theorem bounds_15_3344 : exactInterval 15 3344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3344 : oddCount 3344 15 = 6 ∧ acceleratedOrbit 15 3344 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3344) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3344.1, data_15_3344.2]

/-- Complete interval computation for depth 15, residue 3345. -/
theorem bounds_15_3345 : exactInterval 15 3345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3345 : oddCount 3345 15 = 8 ∧ acceleratedOrbit 15 3345 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3345) = 3 ^ 8 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3345.1, data_15_3345.2]

/-- Complete interval computation for depth 15, residue 3346. -/
theorem bounds_15_3346 : exactInterval 15 3346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3346 : oddCount 3346 15 = 10 ∧ acceleratedOrbit 15 3346 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3346) = 3 ^ 10 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3346.1, data_15_3346.2]

/-- Complete interval computation for depth 15, residue 3347. -/
theorem bounds_15_3347 : exactInterval 15 3347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3347 : oddCount 3347 15 = 10 ∧ acceleratedOrbit 15 3347 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3347) = 3 ^ 10 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3347.1, data_15_3347.2]

/-- Complete interval computation for depth 15, residue 3348. -/
theorem bounds_15_3348 : exactInterval 15 3348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3348 : oddCount 3348 15 = 6 ∧ acceleratedOrbit 15 3348 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3348) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3348.1, data_15_3348.2]

/-- Complete interval computation for depth 15, residue 3349. -/
theorem bounds_15_3349 : exactInterval 15 3349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3349 : oddCount 3349 15 = 6 ∧ acceleratedOrbit 15 3349 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3349) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3349.1, data_15_3349.2]

/-- Complete interval computation for depth 15, residue 3350. -/
theorem bounds_15_3350 : exactInterval 15 3350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3350 : oddCount 3350 15 = 8 ∧ acceleratedOrbit 15 3350 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3350) = 3 ^ 8 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3350.1, data_15_3350.2]

/-- Complete interval computation for depth 15, residue 3351. -/
theorem bounds_15_3351 : exactInterval 15 3351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3351 : oddCount 3351 15 = 8 ∧ acceleratedOrbit 15 3351 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3351) = 3 ^ 8 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3351.1, data_15_3351.2]

/-- Complete interval computation for depth 15, residue 3352. -/
theorem bounds_15_3352 : exactInterval 15 3352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3352 : oddCount 3352 15 = 6 ∧ acceleratedOrbit 15 3352 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3352) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3352.1, data_15_3352.2]

/-- Complete interval computation for depth 15, residue 3353. -/
theorem bounds_15_3353 : exactInterval 15 3353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3353 : oddCount 3353 15 = 7 ∧ acceleratedOrbit 15 3353 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3353) = 3 ^ 7 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3353.1, data_15_3353.2]

/-- Complete interval computation for depth 15, residue 3354. -/
theorem bounds_15_3354 : exactInterval 15 3354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3354 : oddCount 3354 15 = 6 ∧ acceleratedOrbit 15 3354 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3354) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3354.1, data_15_3354.2]

/-- Complete interval computation for depth 15, residue 3355. -/
theorem bounds_15_3355 : exactInterval 15 3355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3355 : oddCount 3355 15 = 11 ∧ acceleratedOrbit 15 3355 = 18146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3355) = 3 ^ 11 * m + 18146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3355.1, data_15_3355.2]

/-- Complete interval computation for depth 15, residue 3356. -/
theorem bounds_15_3356 : exactInterval 15 3356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3356 : oddCount 3356 15 = 9 ∧ acceleratedOrbit 15 3356 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3356) = 3 ^ 9 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3356.1, data_15_3356.2]

/-- Complete interval computation for depth 15, residue 3357. -/
theorem bounds_15_3357 : exactInterval 15 3357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3357 : oddCount 3357 15 = 9 ∧ acceleratedOrbit 15 3357 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3357) = 3 ^ 9 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3357.1, data_15_3357.2]

/-- Complete interval computation for depth 15, residue 3358. -/
theorem bounds_15_3358 : exactInterval 15 3358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3358 : oddCount 3358 15 = 9 ∧ acceleratedOrbit 15 3358 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3358) = 3 ^ 9 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3358.1, data_15_3358.2]

/-- Complete interval computation for depth 15, residue 3359. -/
theorem bounds_15_3359 : exactInterval 15 3359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3359 : oddCount 3359 15 = 8 ∧ acceleratedOrbit 15 3359 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3359) = 3 ^ 8 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3359.1, data_15_3359.2]

/-- Complete interval computation for depth 15, residue 3360. -/
theorem bounds_15_3360 : exactInterval 15 3360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3360 : oddCount 3360 15 = 6 ∧ acceleratedOrbit 15 3360 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3360) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3360.1, data_15_3360.2]

/-- Complete interval computation for depth 15, residue 3361. -/
theorem bounds_15_3361 : exactInterval 15 3361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3361 : oddCount 3361 15 = 5 ∧ acceleratedOrbit 15 3361 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3361) = 3 ^ 5 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3361.1, data_15_3361.2]

/-- Complete interval computation for depth 15, residue 3362. -/
theorem bounds_15_3362 : exactInterval 15 3362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3362 : oddCount 3362 15 = 5 ∧ acceleratedOrbit 15 3362 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3362) = 3 ^ 5 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3362.1, data_15_3362.2]

/-- Complete interval computation for depth 15, residue 3363. -/
theorem bounds_15_3363 : exactInterval 15 3363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3363 : oddCount 3363 15 = 5 ∧ acceleratedOrbit 15 3363 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3363) = 3 ^ 5 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3363.1, data_15_3363.2]

/-- Complete interval computation for depth 15, residue 3364. -/
theorem bounds_15_3364 : exactInterval 15 3364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3364 : oddCount 3364 15 = 5 ∧ acceleratedOrbit 15 3364 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3364) = 3 ^ 5 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3364.1, data_15_3364.2]

/-- Complete interval computation for depth 15, residue 3365. -/
theorem bounds_15_3365 : exactInterval 15 3365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3365 : oddCount 3365 15 = 5 ∧ acceleratedOrbit 15 3365 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3365) = 3 ^ 5 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3365.1, data_15_3365.2]

/-- Complete interval computation for depth 15, residue 3366. -/
theorem bounds_15_3366 : exactInterval 15 3366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3366 : oddCount 3366 15 = 5 ∧ acceleratedOrbit 15 3366 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3366) = 3 ^ 5 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3366.1, data_15_3366.2]

/-- Complete interval computation for depth 15, residue 3367. -/
theorem bounds_15_3367 : exactInterval 15 3367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3367 : oddCount 3367 15 = 10 ∧ acceleratedOrbit 15 3367 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3367) = 3 ^ 10 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3367.1, data_15_3367.2]

/-- Complete interval computation for depth 15, residue 3368. -/
theorem bounds_15_3368 : exactInterval 15 3368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3368 : oddCount 3368 15 = 6 ∧ acceleratedOrbit 15 3368 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3368) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3368.1, data_15_3368.2]

/-- Complete interval computation for depth 15, residue 3369. -/
theorem bounds_15_3369 : exactInterval 15 3369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3369 : oddCount 3369 15 = 12 ∧ acceleratedOrbit 15 3369 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3369) = 3 ^ 12 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3369.1, data_15_3369.2]

/-- Complete interval computation for depth 15, residue 3370. -/
theorem bounds_15_3370 : exactInterval 15 3370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3370 : oddCount 3370 15 = 6 ∧ acceleratedOrbit 15 3370 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3370) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3370.1, data_15_3370.2]

/-- Complete interval computation for depth 15, residue 3371. -/
theorem bounds_15_3371 : exactInterval 15 3371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3371 : oddCount 3371 15 = 8 ∧ acceleratedOrbit 15 3371 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3371) = 3 ^ 8 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3371.1, data_15_3371.2]

/-- Complete interval computation for depth 15, residue 3372. -/
theorem bounds_15_3372 : exactInterval 15 3372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3372 : oddCount 3372 15 = 6 ∧ acceleratedOrbit 15 3372 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3372) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3372.1, data_15_3372.2]

/-- Complete interval computation for depth 15, residue 3373. -/
theorem bounds_15_3373 : exactInterval 15 3373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3373 : oddCount 3373 15 = 6 ∧ acceleratedOrbit 15 3373 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3373) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3373.1, data_15_3373.2]

/-- Complete interval computation for depth 15, residue 3374. -/
theorem bounds_15_3374 : exactInterval 15 3374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3374 : oddCount 3374 15 = 6 ∧ acceleratedOrbit 15 3374 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3374) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3374.1, data_15_3374.2]

end Collatz.Research.PassageAtlas.Batch0103
