import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0353

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2334. -/
theorem bounds_12_2334 : exactInterval 12 2334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2334 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2334) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2334 : oddCount 2334 12 = 6 ∧ acceleratedOrbit 12 2334 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2334 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2334) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2334.1, data_12_2334.2]

/-- Complete interval computation for depth 12, residue 2335. -/
theorem bounds_12_2335 : exactInterval 12 2335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2335 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2335) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2335 : oddCount 2335 12 = 8 ∧ acceleratedOrbit 12 2335 = 3743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2335 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2335) = 3 ^ 8 * m + 3743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2335.1, data_12_2335.2]

/-- Complete interval computation for depth 12, residue 2336. -/
theorem bounds_12_2336 : exactInterval 12 2336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2336 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2336) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2336 : oddCount 2336 12 = 4 ∧ acceleratedOrbit 12 2336 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2336 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2336) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2336.1, data_12_2336.2]

/-- Complete interval computation for depth 12, residue 2337. -/
theorem bounds_12_2337 : exactInterval 12 2337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2337 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2337) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2337 : oddCount 2337 12 = 5 ∧ acceleratedOrbit 12 2337 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2337 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2337) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2337.1, data_12_2337.2]

/-- Complete interval computation for depth 12, residue 2338. -/
theorem bounds_12_2338 : exactInterval 12 2338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2338 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2338) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2338 : oddCount 2338 12 = 6 ∧ acceleratedOrbit 12 2338 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2338 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2338) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2338.1, data_12_2338.2]

/-- Complete interval computation for depth 12, residue 2339. -/
theorem bounds_12_2339 : exactInterval 12 2339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2339 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2339) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2339 : oddCount 2339 12 = 6 ∧ acceleratedOrbit 12 2339 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2339 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2339) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2339.1, data_12_2339.2]

/-- Complete interval computation for depth 12, residue 2340. -/
theorem bounds_12_2340 : exactInterval 12 2340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2340 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2340) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2340 : oddCount 2340 12 = 6 ∧ acceleratedOrbit 12 2340 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2340 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2340) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2340.1, data_12_2340.2]

/-- Complete interval computation for depth 12, residue 2341. -/
theorem bounds_12_2341 : exactInterval 12 2341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2341 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2341) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2341 : oddCount 2341 12 = 6 ∧ acceleratedOrbit 12 2341 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2341 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2341) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2341.1, data_12_2341.2]

/-- Complete interval computation for depth 12, residue 2342. -/
theorem bounds_12_2342 : exactInterval 12 2342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2342 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2342) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2342 : oddCount 2342 12 = 6 ∧ acceleratedOrbit 12 2342 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2342 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2342) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2342.1, data_12_2342.2]

/-- Complete interval computation for depth 12, residue 2343. -/
theorem bounds_12_2343 : exactInterval 12 2343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2343 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2343) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2343 : oddCount 2343 12 = 7 ∧ acceleratedOrbit 12 2343 = 1252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2343 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2343) = 3 ^ 7 * m + 1252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2343.1, data_12_2343.2]

/-- Complete interval computation for depth 12, residue 2344. -/
theorem bounds_12_2344 : exactInterval 12 2344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2344 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2344) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2344 : oddCount 2344 12 = 4 ∧ acceleratedOrbit 12 2344 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2344 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2344) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2344.1, data_12_2344.2]

/-- Complete interval computation for depth 12, residue 2345. -/
theorem bounds_12_2345 : exactInterval 12 2345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2345 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2345) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2345 : oddCount 2345 12 = 7 ∧ acceleratedOrbit 12 2345 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2345 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2345) = 3 ^ 7 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2345.1, data_12_2345.2]

/-- Complete interval computation for depth 12, residue 2346. -/
theorem bounds_12_2346 : exactInterval 12 2346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2346 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2346) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2346 : oddCount 2346 12 = 4 ∧ acceleratedOrbit 12 2346 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2346 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2346) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2346.1, data_12_2346.2]

/-- Complete interval computation for depth 12, residue 2347. -/
theorem bounds_12_2347 : exactInterval 12 2347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2347 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2347) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2347 : oddCount 2347 12 = 7 ∧ acceleratedOrbit 12 2347 = 1255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2347 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2347) = 3 ^ 7 * m + 1255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2347.1, data_12_2347.2]

/-- Complete interval computation for depth 12, residue 2348. -/
theorem bounds_12_2348 : exactInterval 12 2348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2348 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2348) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2348 : oddCount 2348 12 = 4 ∧ acceleratedOrbit 12 2348 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2348 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2348) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2348.1, data_12_2348.2]

/-- Complete interval computation for depth 12, residue 2349. -/
theorem bounds_12_2349 : exactInterval 12 2349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2349 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2349) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2349 : oddCount 2349 12 = 4 ∧ acceleratedOrbit 12 2349 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2349 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2349) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2349.1, data_12_2349.2]

end Collatz.Research.StoppingAtlas.Batch0353
