import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0408

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13336. -/
theorem bounds_15_13336 : exactInterval 15 13336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13336 : oddCount 13336 15 = 3 ∧ acceleratedOrbit 15 13336 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13336) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13336.1, data_15_13336.2]

/-- Complete interval computation for depth 15, residue 13337. -/
theorem bounds_15_13337 : exactInterval 15 13337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13337 : oddCount 13337 15 = 9 ∧ acceleratedOrbit 15 13337 = 8014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13337) = 3 ^ 9 * m + 8014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13337.1, data_15_13337.2]

/-- Complete interval computation for depth 15, residue 13338. -/
theorem bounds_15_13338 : exactInterval 15 13338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13338 : oddCount 13338 15 = 3 ∧ acceleratedOrbit 15 13338 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13338) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13338.1, data_15_13338.2]

/-- Complete interval computation for depth 15, residue 13339. -/
theorem bounds_15_13339 : exactInterval 15 13339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13339 : oddCount 13339 15 = 10 ∧ acceleratedOrbit 15 13339 = 24040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13339) = 3 ^ 10 * m + 24040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13339.1, data_15_13339.2]

/-- Complete interval computation for depth 15, residue 13340. -/
theorem bounds_15_13340 : exactInterval 15 13340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13340 : oddCount 13340 15 = 10 ∧ acceleratedOrbit 15 13340 = 24056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13340) = 3 ^ 10 * m + 24056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13340.1, data_15_13340.2]

/-- Complete interval computation for depth 15, residue 13341. -/
theorem bounds_15_13341 : exactInterval 15 13341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13341 : oddCount 13341 15 = 10 ∧ acceleratedOrbit 15 13341 = 24056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13341) = 3 ^ 10 * m + 24056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13341.1, data_15_13341.2]

/-- Complete interval computation for depth 15, residue 13342. -/
theorem bounds_15_13342 : exactInterval 15 13342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13342 : oddCount 13342 15 = 10 ∧ acceleratedOrbit 15 13342 = 24056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13342) = 3 ^ 10 * m + 24056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13342.1, data_15_13342.2]

/-- Complete interval computation for depth 15, residue 13343. -/
theorem bounds_15_13343 : exactInterval 15 13343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13343 : oddCount 13343 15 = 12 ∧ acceleratedOrbit 15 13343 = 216422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13343) = 3 ^ 12 * m + 216422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13343.1, data_15_13343.2]

/-- Complete interval computation for depth 15, residue 13344. -/
theorem bounds_15_13344 : exactInterval 15 13344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13344 : oddCount 13344 15 = 6 ∧ acceleratedOrbit 15 13344 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13344) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13344.1, data_15_13344.2]

/-- Complete interval computation for depth 15, residue 13345. -/
theorem bounds_15_13345 : exactInterval 15 13345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13345 : oddCount 13345 15 = 11 ∧ acceleratedOrbit 15 13345 = 72170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13345) = 3 ^ 11 * m + 72170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13345.1, data_15_13345.2]

/-- Complete interval computation for depth 15, residue 13346. -/
theorem bounds_15_13346 : exactInterval 15 13346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13346 : oddCount 13346 15 = 3 ∧ acceleratedOrbit 15 13346 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13346) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13346.1, data_15_13346.2]

/-- Complete interval computation for depth 15, residue 13347. -/
theorem bounds_15_13347 : exactInterval 15 13347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13347 : oddCount 13347 15 = 3 ∧ acceleratedOrbit 15 13347 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13347) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13347.1, data_15_13347.2]

/-- Complete interval computation for depth 15, residue 13348. -/
theorem bounds_15_13348 : exactInterval 15 13348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13348 : oddCount 13348 15 = 8 ∧ acceleratedOrbit 15 13348 = 2675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13348) = 3 ^ 8 * m + 2675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13348.1, data_15_13348.2]

/-- Complete interval computation for depth 15, residue 13349. -/
theorem bounds_15_13349 : exactInterval 15 13349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13349 : oddCount 13349 15 = 8 ∧ acceleratedOrbit 15 13349 = 2675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13349) = 3 ^ 8 * m + 2675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13349.1, data_15_13349.2]

/-- Complete interval computation for depth 15, residue 13350. -/
theorem bounds_15_13350 : exactInterval 15 13350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13350 : oddCount 13350 15 = 8 ∧ acceleratedOrbit 15 13350 = 2675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13350) = 3 ^ 8 * m + 2675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13350.1, data_15_13350.2]

/-- Complete interval computation for depth 15, residue 13351. -/
theorem bounds_15_13351 : exactInterval 15 13351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13351 : oddCount 13351 15 = 8 ∧ acceleratedOrbit 15 13351 = 2674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13351) = 3 ^ 8 * m + 2674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13351.1, data_15_13351.2]

/-- Complete interval computation for depth 15, residue 13352. -/
theorem bounds_15_13352 : exactInterval 15 13352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13352 : oddCount 13352 15 = 6 ∧ acceleratedOrbit 15 13352 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13352) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13352.1, data_15_13352.2]

/-- Complete interval computation for depth 15, residue 13353. -/
theorem bounds_15_13353 : exactInterval 15 13353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13353 : oddCount 13353 15 = 8 ∧ acceleratedOrbit 15 13353 = 2674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13353) = 3 ^ 8 * m + 2674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13353.1, data_15_13353.2]

/-- Complete interval computation for depth 15, residue 13354. -/
theorem bounds_15_13354 : exactInterval 15 13354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13354 : oddCount 13354 15 = 6 ∧ acceleratedOrbit 15 13354 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13354) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13354.1, data_15_13354.2]

/-- Complete interval computation for depth 15, residue 13355. -/
theorem bounds_15_13355 : exactInterval 15 13355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13355 : oddCount 13355 15 = 7 ∧ acceleratedOrbit 15 13355 = 892 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13355) = 3 ^ 7 * m + 892 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13355.1, data_15_13355.2]

/-- Complete interval computation for depth 15, residue 13356. -/
theorem bounds_15_13356 : exactInterval 15 13356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13356 : oddCount 13356 15 = 7 ∧ acceleratedOrbit 15 13356 = 893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13356) = 3 ^ 7 * m + 893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13356.1, data_15_13356.2]

/-- Complete interval computation for depth 15, residue 13357. -/
theorem bounds_15_13357 : exactInterval 15 13357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13357 : oddCount 13357 15 = 7 ∧ acceleratedOrbit 15 13357 = 893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13357) = 3 ^ 7 * m + 893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13357.1, data_15_13357.2]

/-- Complete interval computation for depth 15, residue 13358. -/
theorem bounds_15_13358 : exactInterval 15 13358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13358 : oddCount 13358 15 = 7 ∧ acceleratedOrbit 15 13358 = 893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13358) = 3 ^ 7 * m + 893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13358.1, data_15_13358.2]

/-- Complete interval computation for depth 15, residue 13359. -/
theorem bounds_15_13359 : exactInterval 15 13359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13359 : oddCount 13359 15 = 10 ∧ acceleratedOrbit 15 13359 = 24077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13359) = 3 ^ 10 * m + 24077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13359.1, data_15_13359.2]

/-- Complete interval computation for depth 15, residue 13360. -/
theorem bounds_15_13360 : exactInterval 15 13360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13360 : oddCount 13360 15 = 6 ∧ acceleratedOrbit 15 13360 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13360) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13360.1, data_15_13360.2]

/-- Complete interval computation for depth 15, residue 13361. -/
theorem bounds_15_13361 : exactInterval 15 13361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13361 : oddCount 13361 15 = 7 ∧ acceleratedOrbit 15 13361 = 893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13361) = 3 ^ 7 * m + 893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13361.1, data_15_13361.2]

/-- Complete interval computation for depth 15, residue 13362. -/
theorem bounds_15_13362 : exactInterval 15 13362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13362 : oddCount 13362 15 = 7 ∧ acceleratedOrbit 15 13362 = 893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13362) = 3 ^ 7 * m + 893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13362.1, data_15_13362.2]

/-- Complete interval computation for depth 15, residue 13363. -/
theorem bounds_15_13363 : exactInterval 15 13363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13363 : oddCount 13363 15 = 7 ∧ acceleratedOrbit 15 13363 = 893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13363) = 3 ^ 7 * m + 893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13363.1, data_15_13363.2]

/-- Complete interval computation for depth 15, residue 13364. -/
theorem bounds_15_13364 : exactInterval 15 13364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13364 : oddCount 13364 15 = 6 ∧ acceleratedOrbit 15 13364 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13364) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13364.1, data_15_13364.2]

/-- Complete interval computation for depth 15, residue 13365. -/
theorem bounds_15_13365 : exactInterval 15 13365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13365 : oddCount 13365 15 = 6 ∧ acceleratedOrbit 15 13365 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13365) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13365.1, data_15_13365.2]

/-- Complete interval computation for depth 15, residue 13366. -/
theorem bounds_15_13366 : exactInterval 15 13366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13366 : oddCount 13366 15 = 8 ∧ acceleratedOrbit 15 13366 = 2677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13366) = 3 ^ 8 * m + 2677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13366.1, data_15_13366.2]

/-- Complete interval computation for depth 15, residue 13367. -/
theorem bounds_15_13367 : exactInterval 15 13367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13367 : oddCount 13367 15 = 8 ∧ acceleratedOrbit 15 13367 = 2677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13367) = 3 ^ 8 * m + 2677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13367.1, data_15_13367.2]

/-- Complete interval computation for depth 15, residue 13368. -/
theorem bounds_15_13368 : exactInterval 15 13368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13368 : oddCount 13368 15 = 6 ∧ acceleratedOrbit 15 13368 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13368) = 3 ^ 6 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13368.1, data_15_13368.2]

end Collatz.Research.PassageAtlas.Batch0408
