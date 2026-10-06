import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0957

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31326. -/
theorem bounds_15_31326 : exactInterval 15 31326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31326 : oddCount 31326 15 = 11 ∧ acceleratedOrbit 15 31326 = 169370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31326) = 3 ^ 11 * m + 169370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31326.1, data_15_31326.2]

/-- Complete interval computation for depth 15, residue 31327. -/
theorem bounds_15_31327 : exactInterval 15 31327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31327 : oddCount 31327 15 = 11 ∧ acceleratedOrbit 15 31327 = 169370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31327) = 3 ^ 11 * m + 169370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31327.1, data_15_31327.2]

/-- Complete interval computation for depth 15, residue 31328. -/
theorem bounds_15_31328 : exactInterval 15 31328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31328 : oddCount 31328 15 = 7 ∧ acceleratedOrbit 15 31328 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31328) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31328.1, data_15_31328.2]

/-- Complete interval computation for depth 15, residue 31329. -/
theorem bounds_15_31329 : exactInterval 15 31329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31329 : oddCount 31329 15 = 8 ∧ acceleratedOrbit 15 31329 = 6274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31329) = 3 ^ 8 * m + 6274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31329.1, data_15_31329.2]

/-- Complete interval computation for depth 15, residue 31330. -/
theorem bounds_15_31330 : exactInterval 15 31330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31330 : oddCount 31330 15 = 8 ∧ acceleratedOrbit 15 31330 = 6277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31330) = 3 ^ 8 * m + 6277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31330.1, data_15_31330.2]

/-- Complete interval computation for depth 15, residue 31331. -/
theorem bounds_15_31331 : exactInterval 15 31331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31331 : oddCount 31331 15 = 8 ∧ acceleratedOrbit 15 31331 = 6277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31331) = 3 ^ 8 * m + 6277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31331.1, data_15_31331.2]

/-- Complete interval computation for depth 15, residue 31332. -/
theorem bounds_15_31332 : exactInterval 15 31332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31332 : oddCount 31332 15 = 8 ∧ acceleratedOrbit 15 31332 = 6277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31332) = 3 ^ 8 * m + 6277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31332.1, data_15_31332.2]

/-- Complete interval computation for depth 15, residue 31333. -/
theorem bounds_15_31333 : exactInterval 15 31333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31333 : oddCount 31333 15 = 8 ∧ acceleratedOrbit 15 31333 = 6277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31333) = 3 ^ 8 * m + 6277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31333.1, data_15_31333.2]

/-- Complete interval computation for depth 15, residue 31334. -/
theorem bounds_15_31334 : exactInterval 15 31334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31334 : oddCount 31334 15 = 8 ∧ acceleratedOrbit 15 31334 = 6277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31334) = 3 ^ 8 * m + 6277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31334.1, data_15_31334.2]

/-- Complete interval computation for depth 15, residue 31335. -/
theorem bounds_15_31335 : exactInterval 15 31335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31335 : oddCount 31335 15 = 10 ∧ acceleratedOrbit 15 31335 = 56470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31335) = 3 ^ 10 * m + 56470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31335.1, data_15_31335.2]

/-- Complete interval computation for depth 15, residue 31336. -/
theorem bounds_15_31336 : exactInterval 15 31336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31336 : oddCount 31336 15 = 7 ∧ acceleratedOrbit 15 31336 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31336) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31336.1, data_15_31336.2]

/-- Complete interval computation for depth 15, residue 31337. -/
theorem bounds_15_31337 : exactInterval 15 31337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31337 : oddCount 31337 15 = 8 ∧ acceleratedOrbit 15 31337 = 6275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31337) = 3 ^ 8 * m + 6275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31337.1, data_15_31337.2]

/-- Complete interval computation for depth 15, residue 31338. -/
theorem bounds_15_31338 : exactInterval 15 31338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31338 : oddCount 31338 15 = 7 ∧ acceleratedOrbit 15 31338 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31338) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31338.1, data_15_31338.2]

/-- Complete interval computation for depth 15, residue 31339. -/
theorem bounds_15_31339 : exactInterval 15 31339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31339 : oddCount 31339 15 = 7 ∧ acceleratedOrbit 15 31339 = 2092 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31339) = 3 ^ 7 * m + 2092 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31339.1, data_15_31339.2]

/-- Complete interval computation for depth 15, residue 31340. -/
theorem bounds_15_31340 : exactInterval 15 31340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31340 : oddCount 31340 15 = 9 ∧ acceleratedOrbit 15 31340 = 18829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31340) = 3 ^ 9 * m + 18829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31340.1, data_15_31340.2]

/-- Complete interval computation for depth 15, residue 31341. -/
theorem bounds_15_31341 : exactInterval 15 31341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31341 : oddCount 31341 15 = 9 ∧ acceleratedOrbit 15 31341 = 18829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31341) = 3 ^ 9 * m + 18829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31341.1, data_15_31341.2]

/-- Complete interval computation for depth 15, residue 31342. -/
theorem bounds_15_31342 : exactInterval 15 31342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31342 : oddCount 31342 15 = 9 ∧ acceleratedOrbit 15 31342 = 18829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31342) = 3 ^ 9 * m + 18829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31342.1, data_15_31342.2]

/-- Complete interval computation for depth 15, residue 31343. -/
theorem bounds_15_31343 : exactInterval 15 31343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31343 : oddCount 31343 15 = 12 ∧ acceleratedOrbit 15 31343 = 508355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31343) = 3 ^ 12 * m + 508355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31343.1, data_15_31343.2]

/-- Complete interval computation for depth 15, residue 31344. -/
theorem bounds_15_31344 : exactInterval 15 31344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31344 : oddCount 31344 15 = 8 ∧ acceleratedOrbit 15 31344 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31344) = 3 ^ 8 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31344.1, data_15_31344.2]

/-- Complete interval computation for depth 15, residue 31345. -/
theorem bounds_15_31345 : exactInterval 15 31345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31345 : oddCount 31345 15 = 7 ∧ acceleratedOrbit 15 31345 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31345) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31345.1, data_15_31345.2]

/-- Complete interval computation for depth 15, residue 31346. -/
theorem bounds_15_31346 : exactInterval 15 31346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31346 : oddCount 31346 15 = 10 ∧ acceleratedOrbit 15 31346 = 56497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31346) = 3 ^ 10 * m + 56497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31346.1, data_15_31346.2]

/-- Complete interval computation for depth 15, residue 31347. -/
theorem bounds_15_31347 : exactInterval 15 31347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31347 : oddCount 31347 15 = 10 ∧ acceleratedOrbit 15 31347 = 56497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31347) = 3 ^ 10 * m + 56497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31347.1, data_15_31347.2]

/-- Complete interval computation for depth 15, residue 31348. -/
theorem bounds_15_31348 : exactInterval 15 31348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31348 : oddCount 31348 15 = 8 ∧ acceleratedOrbit 15 31348 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31348) = 3 ^ 8 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31348.1, data_15_31348.2]

/-- Complete interval computation for depth 15, residue 31349. -/
theorem bounds_15_31349 : exactInterval 15 31349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31349 : oddCount 31349 15 = 8 ∧ acceleratedOrbit 15 31349 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31349) = 3 ^ 8 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31349.1, data_15_31349.2]

/-- Complete interval computation for depth 15, residue 31350. -/
theorem bounds_15_31350 : exactInterval 15 31350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31350 : oddCount 31350 15 = 5 ∧ acceleratedOrbit 15 31350 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31350) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31350.1, data_15_31350.2]

/-- Complete interval computation for depth 15, residue 31351. -/
theorem bounds_15_31351 : exactInterval 15 31351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31351 : oddCount 31351 15 = 5 ∧ acceleratedOrbit 15 31351 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31351) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31351.1, data_15_31351.2]

/-- Complete interval computation for depth 15, residue 31352. -/
theorem bounds_15_31352 : exactInterval 15 31352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31352 : oddCount 31352 15 = 8 ∧ acceleratedOrbit 15 31352 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31352) = 3 ^ 8 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31352.1, data_15_31352.2]

/-- Complete interval computation for depth 15, residue 31353. -/
theorem bounds_15_31353 : exactInterval 15 31353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31353 : oddCount 31353 15 = 9 ∧ acceleratedOrbit 15 31353 = 18836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31353) = 3 ^ 9 * m + 18836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31353.1, data_15_31353.2]

/-- Complete interval computation for depth 15, residue 31354. -/
theorem bounds_15_31354 : exactInterval 15 31354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31354 : oddCount 31354 15 = 8 ∧ acceleratedOrbit 15 31354 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31354) = 3 ^ 8 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31354.1, data_15_31354.2]

/-- Complete interval computation for depth 15, residue 31355. -/
theorem bounds_15_31355 : exactInterval 15 31355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31355 : oddCount 31355 15 = 7 ∧ acceleratedOrbit 15 31355 = 2093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31355) = 3 ^ 7 * m + 2093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31355.1, data_15_31355.2]

/-- Complete interval computation for depth 15, residue 31356. -/
theorem bounds_15_31356 : exactInterval 15 31356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31356 : oddCount 31356 15 = 10 ∧ acceleratedOrbit 15 31356 = 56513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31356) = 3 ^ 10 * m + 56513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31356.1, data_15_31356.2]

/-- Complete interval computation for depth 15, residue 31357. -/
theorem bounds_15_31357 : exactInterval 15 31357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31357 : oddCount 31357 15 = 10 ∧ acceleratedOrbit 15 31357 = 56513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31357) = 3 ^ 10 * m + 56513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31357.1, data_15_31357.2]

end Collatz.Research.PassageAtlas.Batch0957
