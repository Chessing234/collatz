import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0927

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30343. -/
theorem bounds_15_30343 : exactInterval 15 30343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30343 : oddCount 30343 15 = 8 ∧ acceleratedOrbit 15 30343 = 6077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30343) = 3 ^ 8 * m + 6077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30343.1, data_15_30343.2]

/-- Complete interval computation for depth 15, residue 30344. -/
theorem bounds_15_30344 : exactInterval 15 30344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30344 : oddCount 30344 15 = 6 ∧ acceleratedOrbit 15 30344 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30344) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30344.1, data_15_30344.2]

/-- Complete interval computation for depth 15, residue 30345. -/
theorem bounds_15_30345 : exactInterval 15 30345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30345 : oddCount 30345 15 = 9 ∧ acceleratedOrbit 15 30345 = 18229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30345) = 3 ^ 9 * m + 18229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30345.1, data_15_30345.2]

/-- Complete interval computation for depth 15, residue 30346. -/
theorem bounds_15_30346 : exactInterval 15 30346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30346 : oddCount 30346 15 = 6 ∧ acceleratedOrbit 15 30346 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30346) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30346.1, data_15_30346.2]

/-- Complete interval computation for depth 15, residue 30347. -/
theorem bounds_15_30347 : exactInterval 15 30347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30347 : oddCount 30347 15 = 7 ∧ acceleratedOrbit 15 30347 = 2026 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30347) = 3 ^ 7 * m + 2026 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30347.1, data_15_30347.2]

/-- Complete interval computation for depth 15, residue 30348. -/
theorem bounds_15_30348 : exactInterval 15 30348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30348 : oddCount 30348 15 = 6 ∧ acceleratedOrbit 15 30348 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30348) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30348.1, data_15_30348.2]

/-- Complete interval computation for depth 15, residue 30349. -/
theorem bounds_15_30349 : exactInterval 15 30349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30349 : oddCount 30349 15 = 6 ∧ acceleratedOrbit 15 30349 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30349) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30349.1, data_15_30349.2]

/-- Complete interval computation for depth 15, residue 30350. -/
theorem bounds_15_30350 : exactInterval 15 30350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30350 : oddCount 30350 15 = 9 ∧ acceleratedOrbit 15 30350 = 18233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30350) = 3 ^ 9 * m + 18233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30350.1, data_15_30350.2]

/-- Complete interval computation for depth 15, residue 30351. -/
theorem bounds_15_30351 : exactInterval 15 30351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30351 : oddCount 30351 15 = 9 ∧ acceleratedOrbit 15 30351 = 18233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30351) = 3 ^ 9 * m + 18233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30351.1, data_15_30351.2]

/-- Complete interval computation for depth 15, residue 30352. -/
theorem bounds_15_30352 : exactInterval 15 30352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30352 : oddCount 30352 15 = 6 ∧ acceleratedOrbit 15 30352 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30352) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30352.1, data_15_30352.2]

/-- Complete interval computation for depth 15, residue 30353. -/
theorem bounds_15_30353 : exactInterval 15 30353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30353 : oddCount 30353 15 = 7 ∧ acceleratedOrbit 15 30353 = 2027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30353) = 3 ^ 7 * m + 2027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30353.1, data_15_30353.2]

/-- Complete interval computation for depth 15, residue 30354. -/
theorem bounds_15_30354 : exactInterval 15 30354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30354 : oddCount 30354 15 = 7 ∧ acceleratedOrbit 15 30354 = 2027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30354) = 3 ^ 7 * m + 2027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30354.1, data_15_30354.2]

/-- Complete interval computation for depth 15, residue 30355. -/
theorem bounds_15_30355 : exactInterval 15 30355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30355 : oddCount 30355 15 = 7 ∧ acceleratedOrbit 15 30355 = 2027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30355) = 3 ^ 7 * m + 2027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30355.1, data_15_30355.2]

/-- Complete interval computation for depth 15, residue 30356. -/
theorem bounds_15_30356 : exactInterval 15 30356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30356 : oddCount 30356 15 = 6 ∧ acceleratedOrbit 15 30356 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30356) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30356.1, data_15_30356.2]

/-- Complete interval computation for depth 15, residue 30357. -/
theorem bounds_15_30357 : exactInterval 15 30357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30357 : oddCount 30357 15 = 6 ∧ acceleratedOrbit 15 30357 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30357) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30357.1, data_15_30357.2]

/-- Complete interval computation for depth 15, residue 30358. -/
theorem bounds_15_30358 : exactInterval 15 30358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30358 : oddCount 30358 15 = 6 ∧ acceleratedOrbit 15 30358 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30358) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30358.1, data_15_30358.2]

/-- Complete interval computation for depth 15, residue 30359. -/
theorem bounds_15_30359 : exactInterval 15 30359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30359 : oddCount 30359 15 = 6 ∧ acceleratedOrbit 15 30359 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30359) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30359.1, data_15_30359.2]

/-- Complete interval computation for depth 15, residue 30360. -/
theorem bounds_15_30360 : exactInterval 15 30360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30360 : oddCount 30360 15 = 6 ∧ acceleratedOrbit 15 30360 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30360) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30360.1, data_15_30360.2]

/-- Complete interval computation for depth 15, residue 30361. -/
theorem bounds_15_30361 : exactInterval 15 30361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30361 : oddCount 30361 15 = 8 ∧ acceleratedOrbit 15 30361 = 6080 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30361) = 3 ^ 8 * m + 6080 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30361.1, data_15_30361.2]

/-- Complete interval computation for depth 15, residue 30362. -/
theorem bounds_15_30362 : exactInterval 15 30362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30362 : oddCount 30362 15 = 6 ∧ acceleratedOrbit 15 30362 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30362) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30362.1, data_15_30362.2]

/-- Complete interval computation for depth 15, residue 30363. -/
theorem bounds_15_30363 : exactInterval 15 30363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30363 : oddCount 30363 15 = 10 ∧ acceleratedOrbit 15 30363 = 54719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30363) = 3 ^ 10 * m + 54719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30363.1, data_15_30363.2]

/-- Complete interval computation for depth 15, residue 30364. -/
theorem bounds_15_30364 : exactInterval 15 30364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30364 : oddCount 30364 15 = 7 ∧ acceleratedOrbit 15 30364 = 2027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30364) = 3 ^ 7 * m + 2027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30364.1, data_15_30364.2]

/-- Complete interval computation for depth 15, residue 30365. -/
theorem bounds_15_30365 : exactInterval 15 30365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30365 : oddCount 30365 15 = 7 ∧ acceleratedOrbit 15 30365 = 2027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30365) = 3 ^ 7 * m + 2027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30365.1, data_15_30365.2]

/-- Complete interval computation for depth 15, residue 30366. -/
theorem bounds_15_30366 : exactInterval 15 30366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30366 : oddCount 30366 15 = 7 ∧ acceleratedOrbit 15 30366 = 2027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30366) = 3 ^ 7 * m + 2027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30366.1, data_15_30366.2]

/-- Complete interval computation for depth 15, residue 30367. -/
theorem bounds_15_30367 : exactInterval 15 30367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30367 : oddCount 30367 15 = 12 ∧ acceleratedOrbit 15 30367 = 492520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30367) = 3 ^ 12 * m + 492520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30367.1, data_15_30367.2]

/-- Complete interval computation for depth 15, residue 30368. -/
theorem bounds_15_30368 : exactInterval 15 30368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30368 : oddCount 30368 15 = 4 ∧ acceleratedOrbit 15 30368 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30368) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30368.1, data_15_30368.2]

/-- Complete interval computation for depth 15, residue 30369. -/
theorem bounds_15_30369 : exactInterval 15 30369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30369 : oddCount 30369 15 = 9 ∧ acceleratedOrbit 15 30369 = 18245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30369) = 3 ^ 9 * m + 18245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30369.1, data_15_30369.2]

/-- Complete interval computation for depth 15, residue 30370. -/
theorem bounds_15_30370 : exactInterval 15 30370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30370 : oddCount 30370 15 = 8 ∧ acceleratedOrbit 15 30370 = 6083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30370) = 3 ^ 8 * m + 6083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30370.1, data_15_30370.2]

/-- Complete interval computation for depth 15, residue 30371. -/
theorem bounds_15_30371 : exactInterval 15 30371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30371 : oddCount 30371 15 = 8 ∧ acceleratedOrbit 15 30371 = 6083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30371) = 3 ^ 8 * m + 6083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30371.1, data_15_30371.2]

/-- Complete interval computation for depth 15, residue 30372. -/
theorem bounds_15_30372 : exactInterval 15 30372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30372 : oddCount 30372 15 = 8 ∧ acceleratedOrbit 15 30372 = 6083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30372) = 3 ^ 8 * m + 6083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30372.1, data_15_30372.2]

/-- Complete interval computation for depth 15, residue 30373. -/
theorem bounds_15_30373 : exactInterval 15 30373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30373 : oddCount 30373 15 = 8 ∧ acceleratedOrbit 15 30373 = 6083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30373) = 3 ^ 8 * m + 6083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30373.1, data_15_30373.2]

/-- Complete interval computation for depth 15, residue 30374. -/
theorem bounds_15_30374 : exactInterval 15 30374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30374 : oddCount 30374 15 = 8 ∧ acceleratedOrbit 15 30374 = 6083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30374) = 3 ^ 8 * m + 6083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30374.1, data_15_30374.2]

end Collatz.Research.PassageAtlas.Batch0927
