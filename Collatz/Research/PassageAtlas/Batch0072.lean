import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0072

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2326. -/
theorem bounds_15_2326 : exactInterval 15 2326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2326 : oddCount 2326 15 = 9 ∧ acceleratedOrbit 15 2326 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2326) = 3 ^ 9 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2326.1, data_15_2326.2]

/-- Complete interval computation for depth 15, residue 2327. -/
theorem bounds_15_2327 : exactInterval 15 2327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2327 : oddCount 2327 15 = 9 ∧ acceleratedOrbit 15 2327 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2327) = 3 ^ 9 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2327.1, data_15_2327.2]

/-- Complete interval computation for depth 15, residue 2328. -/
theorem bounds_15_2328 : exactInterval 15 2328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2328 : oddCount 2328 15 = 7 ∧ acceleratedOrbit 15 2328 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2328) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2328.1, data_15_2328.2]

/-- Complete interval computation for depth 15, residue 2329. -/
theorem bounds_15_2329 : exactInterval 15 2329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2329 : oddCount 2329 15 = 9 ∧ acceleratedOrbit 15 2329 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2329) = 3 ^ 9 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2329.1, data_15_2329.2]

/-- Complete interval computation for depth 15, residue 2330. -/
theorem bounds_15_2330 : exactInterval 15 2330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2330 : oddCount 2330 15 = 7 ∧ acceleratedOrbit 15 2330 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2330) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2330.1, data_15_2330.2]

/-- Complete interval computation for depth 15, residue 2331. -/
theorem bounds_15_2331 : exactInterval 15 2331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2331 : oddCount 2331 15 = 8 ∧ acceleratedOrbit 15 2331 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2331) = 3 ^ 8 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2331.1, data_15_2331.2]

/-- Complete interval computation for depth 15, residue 2332. -/
theorem bounds_15_2332 : exactInterval 15 2332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2332 : oddCount 2332 15 = 6 ∧ acceleratedOrbit 15 2332 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2332) = 3 ^ 6 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2332.1, data_15_2332.2]

/-- Complete interval computation for depth 15, residue 2333. -/
theorem bounds_15_2333 : exactInterval 15 2333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2333 : oddCount 2333 15 = 6 ∧ acceleratedOrbit 15 2333 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2333) = 3 ^ 6 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2333.1, data_15_2333.2]

/-- Complete interval computation for depth 15, residue 2334. -/
theorem bounds_15_2334 : exactInterval 15 2334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2334 : oddCount 2334 15 = 6 ∧ acceleratedOrbit 15 2334 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2334) = 3 ^ 6 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2334.1, data_15_2334.2]

/-- Complete interval computation for depth 15, residue 2335. -/
theorem bounds_15_2335 : exactInterval 15 2335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2335 : oddCount 2335 15 = 11 ∧ acceleratedOrbit 15 2335 = 12635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2335) = 3 ^ 11 * m + 12635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2335.1, data_15_2335.2]

/-- Complete interval computation for depth 15, residue 2336. -/
theorem bounds_15_2336 : exactInterval 15 2336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2336 : oddCount 2336 15 = 7 ∧ acceleratedOrbit 15 2336 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2336) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2336.1, data_15_2336.2]

/-- Complete interval computation for depth 15, residue 2337. -/
theorem bounds_15_2337 : exactInterval 15 2337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2337 : oddCount 2337 15 = 7 ∧ acceleratedOrbit 15 2337 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2337) = 3 ^ 7 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2337.1, data_15_2337.2]

/-- Complete interval computation for depth 15, residue 2338. -/
theorem bounds_15_2338 : exactInterval 15 2338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2338 : oddCount 2338 15 = 7 ∧ acceleratedOrbit 15 2338 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2338) = 3 ^ 7 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2338.1, data_15_2338.2]

/-- Complete interval computation for depth 15, residue 2339. -/
theorem bounds_15_2339 : exactInterval 15 2339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2339 : oddCount 2339 15 = 7 ∧ acceleratedOrbit 15 2339 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2339) = 3 ^ 7 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2339.1, data_15_2339.2]

/-- Complete interval computation for depth 15, residue 2340. -/
theorem bounds_15_2340 : exactInterval 15 2340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2340 : oddCount 2340 15 = 7 ∧ acceleratedOrbit 15 2340 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2340) = 3 ^ 7 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2340.1, data_15_2340.2]

/-- Complete interval computation for depth 15, residue 2341. -/
theorem bounds_15_2341 : exactInterval 15 2341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2341 : oddCount 2341 15 = 7 ∧ acceleratedOrbit 15 2341 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2341) = 3 ^ 7 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2341.1, data_15_2341.2]

/-- Complete interval computation for depth 15, residue 2342. -/
theorem bounds_15_2342 : exactInterval 15 2342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2342 : oddCount 2342 15 = 7 ∧ acceleratedOrbit 15 2342 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2342) = 3 ^ 7 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2342.1, data_15_2342.2]

/-- Complete interval computation for depth 15, residue 2343. -/
theorem bounds_15_2343 : exactInterval 15 2343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2343 : oddCount 2343 15 = 8 ∧ acceleratedOrbit 15 2343 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2343) = 3 ^ 8 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2343.1, data_15_2343.2]

/-- Complete interval computation for depth 15, residue 2344. -/
theorem bounds_15_2344 : exactInterval 15 2344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2344 : oddCount 2344 15 = 7 ∧ acceleratedOrbit 15 2344 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2344) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2344.1, data_15_2344.2]

/-- Complete interval computation for depth 15, residue 2345. -/
theorem bounds_15_2345 : exactInterval 15 2345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2345 : oddCount 2345 15 = 8 ∧ acceleratedOrbit 15 2345 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2345) = 3 ^ 8 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2345.1, data_15_2345.2]

/-- Complete interval computation for depth 15, residue 2346. -/
theorem bounds_15_2346 : exactInterval 15 2346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2346 : oddCount 2346 15 = 7 ∧ acceleratedOrbit 15 2346 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2346) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2346.1, data_15_2346.2]

/-- Complete interval computation for depth 15, residue 2347. -/
theorem bounds_15_2347 : exactInterval 15 2347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2347 : oddCount 2347 15 = 10 ∧ acceleratedOrbit 15 2347 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2347) = 3 ^ 10 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2347.1, data_15_2347.2]

/-- Complete interval computation for depth 15, residue 2348. -/
theorem bounds_15_2348 : exactInterval 15 2348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2348 : oddCount 2348 15 = 7 ∧ acceleratedOrbit 15 2348 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2348) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2348.1, data_15_2348.2]

/-- Complete interval computation for depth 15, residue 2349. -/
theorem bounds_15_2349 : exactInterval 15 2349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2349 : oddCount 2349 15 = 7 ∧ acceleratedOrbit 15 2349 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2349) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2349.1, data_15_2349.2]

/-- Complete interval computation for depth 15, residue 2350. -/
theorem bounds_15_2350 : exactInterval 15 2350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2350 : oddCount 2350 15 = 7 ∧ acceleratedOrbit 15 2350 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2350) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2350.1, data_15_2350.2]

/-- Complete interval computation for depth 15, residue 2351. -/
theorem bounds_15_2351 : exactInterval 15 2351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2351 : oddCount 2351 15 = 7 ∧ acceleratedOrbit 15 2351 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2351) = 3 ^ 7 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2351.1, data_15_2351.2]

/-- Complete interval computation for depth 15, residue 2352. -/
theorem bounds_15_2352 : exactInterval 15 2352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2352 : oddCount 2352 15 = 7 ∧ acceleratedOrbit 15 2352 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2352) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2352.1, data_15_2352.2]

/-- Complete interval computation for depth 15, residue 2353. -/
theorem bounds_15_2353 : exactInterval 15 2353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2353 : oddCount 2353 15 = 6 ∧ acceleratedOrbit 15 2353 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2353) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2353.1, data_15_2353.2]

/-- Complete interval computation for depth 15, residue 2354. -/
theorem bounds_15_2354 : exactInterval 15 2354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2354 : oddCount 2354 15 = 6 ∧ acceleratedOrbit 15 2354 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2354) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2354.1, data_15_2354.2]

/-- Complete interval computation for depth 15, residue 2355. -/
theorem bounds_15_2355 : exactInterval 15 2355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2355 : oddCount 2355 15 = 6 ∧ acceleratedOrbit 15 2355 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2355) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2355.1, data_15_2355.2]

/-- Complete interval computation for depth 15, residue 2356. -/
theorem bounds_15_2356 : exactInterval 15 2356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2356 : oddCount 2356 15 = 7 ∧ acceleratedOrbit 15 2356 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2356) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2356.1, data_15_2356.2]

/-- Complete interval computation for depth 15, residue 2357. -/
theorem bounds_15_2357 : exactInterval 15 2357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2357 : oddCount 2357 15 = 7 ∧ acceleratedOrbit 15 2357 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2357) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2357.1, data_15_2357.2]

/-- Complete interval computation for depth 15, residue 2358. -/
theorem bounds_15_2358 : exactInterval 15 2358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2358 : oddCount 2358 15 = 10 ∧ acceleratedOrbit 15 2358 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2358) = 3 ^ 10 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2358.1, data_15_2358.2]

end Collatz.Research.PassageAtlas.Batch0072
