import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0286

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9338. -/
theorem bounds_15_9338 : exactInterval 15 9338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9338 : oddCount 9338 15 = 6 ∧ acceleratedOrbit 15 9338 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9338) = 3 ^ 6 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9338.1, data_15_9338.2]

/-- Complete interval computation for depth 15, residue 9339. -/
theorem bounds_15_9339 : exactInterval 15 9339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9339 : oddCount 9339 15 = 8 ∧ acceleratedOrbit 15 9339 = 1871 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9339) = 3 ^ 8 * m + 1871 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9339.1, data_15_9339.2]

/-- Complete interval computation for depth 15, residue 9340. -/
theorem bounds_15_9340 : exactInterval 15 9340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9340 : oddCount 9340 15 = 9 ∧ acceleratedOrbit 15 9340 = 5615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9340) = 3 ^ 9 * m + 5615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9340.1, data_15_9340.2]

/-- Complete interval computation for depth 15, residue 9341. -/
theorem bounds_15_9341 : exactInterval 15 9341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9341 : oddCount 9341 15 = 9 ∧ acceleratedOrbit 15 9341 = 5615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9341) = 3 ^ 9 * m + 5615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9341.1, data_15_9341.2]

/-- Complete interval computation for depth 15, residue 9342. -/
theorem bounds_15_9342 : exactInterval 15 9342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9342 : oddCount 9342 15 = 9 ∧ acceleratedOrbit 15 9342 = 5615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9342) = 3 ^ 9 * m + 5615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9342.1, data_15_9342.2]

/-- Complete interval computation for depth 15, residue 9343. -/
theorem bounds_15_9343 : exactInterval 15 9343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9343 : oddCount 9343 15 = 11 ∧ acceleratedOrbit 15 9343 = 50516 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9343) = 3 ^ 11 * m + 50516 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9343.1, data_15_9343.2]

/-- Complete interval computation for depth 15, residue 9344. -/
theorem bounds_15_9344 : exactInterval 15 9344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9344 : oddCount 9344 15 = 5 ∧ acceleratedOrbit 15 9344 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9344) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9344.1, data_15_9344.2]

/-- Complete interval computation for depth 15, residue 9345. -/
theorem bounds_15_9345 : exactInterval 15 9345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9345 : oddCount 9345 15 = 11 ∧ acceleratedOrbit 15 9345 = 50543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9345) = 3 ^ 11 * m + 50543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9345.1, data_15_9345.2]

/-- Complete interval computation for depth 15, residue 9346. -/
theorem bounds_15_9346 : exactInterval 15 9346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9346 : oddCount 9346 15 = 6 ∧ acceleratedOrbit 15 9346 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9346) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9346.1, data_15_9346.2]

/-- Complete interval computation for depth 15, residue 9347. -/
theorem bounds_15_9347 : exactInterval 15 9347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9347 : oddCount 9347 15 = 6 ∧ acceleratedOrbit 15 9347 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9347) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9347.1, data_15_9347.2]

/-- Complete interval computation for depth 15, residue 9348. -/
theorem bounds_15_9348 : exactInterval 15 9348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9348 : oddCount 9348 15 = 6 ∧ acceleratedOrbit 15 9348 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9348) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9348.1, data_15_9348.2]

/-- Complete interval computation for depth 15, residue 9349. -/
theorem bounds_15_9349 : exactInterval 15 9349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9349 : oddCount 9349 15 = 6 ∧ acceleratedOrbit 15 9349 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9349) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9349.1, data_15_9349.2]

/-- Complete interval computation for depth 15, residue 9350. -/
theorem bounds_15_9350 : exactInterval 15 9350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9350 : oddCount 9350 15 = 6 ∧ acceleratedOrbit 15 9350 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9350) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9350.1, data_15_9350.2]

/-- Complete interval computation for depth 15, residue 9351. -/
theorem bounds_15_9351 : exactInterval 15 9351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9351 : oddCount 9351 15 = 8 ∧ acceleratedOrbit 15 9351 = 1873 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9351) = 3 ^ 8 * m + 1873 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9351.1, data_15_9351.2]

/-- Complete interval computation for depth 15, residue 9352. -/
theorem bounds_15_9352 : exactInterval 15 9352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9352 : oddCount 9352 15 = 6 ∧ acceleratedOrbit 15 9352 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9352) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9352.1, data_15_9352.2]

/-- Complete interval computation for depth 15, residue 9353. -/
theorem bounds_15_9353 : exactInterval 15 9353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9353 : oddCount 9353 15 = 10 ∧ acceleratedOrbit 15 9353 = 16858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9353) = 3 ^ 10 * m + 16858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9353.1, data_15_9353.2]

/-- Complete interval computation for depth 15, residue 9354. -/
theorem bounds_15_9354 : exactInterval 15 9354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9354 : oddCount 9354 15 = 6 ∧ acceleratedOrbit 15 9354 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9354) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9354.1, data_15_9354.2]

/-- Complete interval computation for depth 15, residue 9355. -/
theorem bounds_15_9355 : exactInterval 15 9355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9355 : oddCount 9355 15 = 8 ∧ acceleratedOrbit 15 9355 = 1874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9355) = 3 ^ 8 * m + 1874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9355.1, data_15_9355.2]

/-- Complete interval computation for depth 15, residue 9356. -/
theorem bounds_15_9356 : exactInterval 15 9356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9356 : oddCount 9356 15 = 6 ∧ acceleratedOrbit 15 9356 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9356) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9356.1, data_15_9356.2]

/-- Complete interval computation for depth 15, residue 9357. -/
theorem bounds_15_9357 : exactInterval 15 9357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9357 : oddCount 9357 15 = 6 ∧ acceleratedOrbit 15 9357 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9357) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9357.1, data_15_9357.2]

/-- Complete interval computation for depth 15, residue 9358. -/
theorem bounds_15_9358 : exactInterval 15 9358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9358 : oddCount 9358 15 = 7 ∧ acceleratedOrbit 15 9358 = 625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9358) = 3 ^ 7 * m + 625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9358.1, data_15_9358.2]

/-- Complete interval computation for depth 15, residue 9359. -/
theorem bounds_15_9359 : exactInterval 15 9359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9359 : oddCount 9359 15 = 7 ∧ acceleratedOrbit 15 9359 = 625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9359) = 3 ^ 7 * m + 625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9359.1, data_15_9359.2]

/-- Complete interval computation for depth 15, residue 9360. -/
theorem bounds_15_9360 : exactInterval 15 9360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9360 : oddCount 9360 15 = 6 ∧ acceleratedOrbit 15 9360 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9360) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9360.1, data_15_9360.2]

/-- Complete interval computation for depth 15, residue 9361. -/
theorem bounds_15_9361 : exactInterval 15 9361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9361 : oddCount 9361 15 = 8 ∧ acceleratedOrbit 15 9361 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9361) = 3 ^ 8 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9361.1, data_15_9361.2]

/-- Complete interval computation for depth 15, residue 9362. -/
theorem bounds_15_9362 : exactInterval 15 9362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9362 : oddCount 9362 15 = 8 ∧ acceleratedOrbit 15 9362 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9362) = 3 ^ 8 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9362.1, data_15_9362.2]

/-- Complete interval computation for depth 15, residue 9363. -/
theorem bounds_15_9363 : exactInterval 15 9363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9363 : oddCount 9363 15 = 8 ∧ acceleratedOrbit 15 9363 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9363) = 3 ^ 8 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9363.1, data_15_9363.2]

/-- Complete interval computation for depth 15, residue 9364. -/
theorem bounds_15_9364 : exactInterval 15 9364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9364 : oddCount 9364 15 = 6 ∧ acceleratedOrbit 15 9364 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9364) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9364.1, data_15_9364.2]

/-- Complete interval computation for depth 15, residue 9365. -/
theorem bounds_15_9365 : exactInterval 15 9365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9365 : oddCount 9365 15 = 6 ∧ acceleratedOrbit 15 9365 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9365) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9365.1, data_15_9365.2]

/-- Complete interval computation for depth 15, residue 9366. -/
theorem bounds_15_9366 : exactInterval 15 9366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9366 : oddCount 9366 15 = 6 ∧ acceleratedOrbit 15 9366 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9366) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9366.1, data_15_9366.2]

/-- Complete interval computation for depth 15, residue 9367. -/
theorem bounds_15_9367 : exactInterval 15 9367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9367 : oddCount 9367 15 = 6 ∧ acceleratedOrbit 15 9367 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9367) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9367.1, data_15_9367.2]

/-- Complete interval computation for depth 15, residue 9368. -/
theorem bounds_15_9368 : exactInterval 15 9368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9368 : oddCount 9368 15 = 6 ∧ acceleratedOrbit 15 9368 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9368) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9368.1, data_15_9368.2]

/-- Complete interval computation for depth 15, residue 9369. -/
theorem bounds_15_9369 : exactInterval 15 9369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9369 : oddCount 9369 15 = 6 ∧ acceleratedOrbit 15 9369 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9369) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9369.1, data_15_9369.2]

/-- Complete interval computation for depth 15, residue 9370. -/
theorem bounds_15_9370 : exactInterval 15 9370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9370 : oddCount 9370 15 = 6 ∧ acceleratedOrbit 15 9370 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9370) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9370.1, data_15_9370.2]

end Collatz.Research.PassageAtlas.Batch0286
