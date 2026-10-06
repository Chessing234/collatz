import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0499

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16318. -/
theorem bounds_15_16318 : exactInterval 15 16318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16318 : oddCount 16318 15 = 8 ∧ acceleratedOrbit 15 16318 = 3268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16318) = 3 ^ 8 * m + 3268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16318.1, data_15_16318.2]

/-- Complete interval computation for depth 15, residue 16319. -/
theorem bounds_15_16319 : exactInterval 15 16319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16319 : oddCount 16319 15 = 11 ∧ acceleratedOrbit 15 16319 = 88229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16319) = 3 ^ 11 * m + 88229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16319.1, data_15_16319.2]

/-- Complete interval computation for depth 15, residue 16320. -/
theorem bounds_15_16320 : exactInterval 15 16320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16320 : oddCount 16320 15 = 8 ∧ acceleratedOrbit 15 16320 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16320) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16320.1, data_15_16320.2]

/-- Complete interval computation for depth 15, residue 16321. -/
theorem bounds_15_16321 : exactInterval 15 16321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16321 : oddCount 16321 15 = 7 ∧ acceleratedOrbit 15 16321 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16321) = 3 ^ 7 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16321.1, data_15_16321.2]

/-- Complete interval computation for depth 15, residue 16322. -/
theorem bounds_15_16322 : exactInterval 15 16322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16322 : oddCount 16322 15 = 10 ∧ acceleratedOrbit 15 16322 = 29423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16322) = 3 ^ 10 * m + 29423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16322.1, data_15_16322.2]

/-- Complete interval computation for depth 15, residue 16323. -/
theorem bounds_15_16323 : exactInterval 15 16323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16323 : oddCount 16323 15 = 10 ∧ acceleratedOrbit 15 16323 = 29423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16323) = 3 ^ 10 * m + 29423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16323.1, data_15_16323.2]

/-- Complete interval computation for depth 15, residue 16324. -/
theorem bounds_15_16324 : exactInterval 15 16324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16324 : oddCount 16324 15 = 7 ∧ acceleratedOrbit 15 16324 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16324) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16324.1, data_15_16324.2]

/-- Complete interval computation for depth 15, residue 16325. -/
theorem bounds_15_16325 : exactInterval 15 16325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16325 : oddCount 16325 15 = 7 ∧ acceleratedOrbit 15 16325 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16325) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16325.1, data_15_16325.2]

/-- Complete interval computation for depth 15, residue 16326. -/
theorem bounds_15_16326 : exactInterval 15 16326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16326 : oddCount 16326 15 = 7 ∧ acceleratedOrbit 15 16326 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16326) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16326.1, data_15_16326.2]

/-- Complete interval computation for depth 15, residue 16327. -/
theorem bounds_15_16327 : exactInterval 15 16327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16327 : oddCount 16327 15 = 9 ∧ acceleratedOrbit 15 16327 = 9809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16327) = 3 ^ 9 * m + 9809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16327.1, data_15_16327.2]

/-- Complete interval computation for depth 15, residue 16328. -/
theorem bounds_15_16328 : exactInterval 15 16328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16328 : oddCount 16328 15 = 7 ∧ acceleratedOrbit 15 16328 = 1091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16328) = 3 ^ 7 * m + 1091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16328.1, data_15_16328.2]

/-- Complete interval computation for depth 15, residue 16329. -/
theorem bounds_15_16329 : exactInterval 15 16329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16329 : oddCount 16329 15 = 9 ∧ acceleratedOrbit 15 16329 = 9811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16329) = 3 ^ 9 * m + 9811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16329.1, data_15_16329.2]

/-- Complete interval computation for depth 15, residue 16330. -/
theorem bounds_15_16330 : exactInterval 15 16330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16330 : oddCount 16330 15 = 7 ∧ acceleratedOrbit 15 16330 = 1091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16330) = 3 ^ 7 * m + 1091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16330.1, data_15_16330.2]

/-- Complete interval computation for depth 15, residue 16331. -/
theorem bounds_15_16331 : exactInterval 15 16331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16331 : oddCount 16331 15 = 6 ∧ acceleratedOrbit 15 16331 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16331) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16331.1, data_15_16331.2]

/-- Complete interval computation for depth 15, residue 16332. -/
theorem bounds_15_16332 : exactInterval 15 16332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16332 : oddCount 16332 15 = 7 ∧ acceleratedOrbit 15 16332 = 1091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16332) = 3 ^ 7 * m + 1091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16332.1, data_15_16332.2]

/-- Complete interval computation for depth 15, residue 16333. -/
theorem bounds_15_16333 : exactInterval 15 16333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16333 : oddCount 16333 15 = 7 ∧ acceleratedOrbit 15 16333 = 1091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16333) = 3 ^ 7 * m + 1091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16333.1, data_15_16333.2]

/-- Complete interval computation for depth 15, residue 16334. -/
theorem bounds_15_16334 : exactInterval 15 16334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16334 : oddCount 16334 15 = 9 ∧ acceleratedOrbit 15 16334 = 9814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16334) = 3 ^ 9 * m + 9814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16334.1, data_15_16334.2]

/-- Complete interval computation for depth 15, residue 16335. -/
theorem bounds_15_16335 : exactInterval 15 16335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16335 : oddCount 16335 15 = 9 ∧ acceleratedOrbit 15 16335 = 9814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16335) = 3 ^ 9 * m + 9814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16335.1, data_15_16335.2]

/-- Complete interval computation for depth 15, residue 16336. -/
theorem bounds_15_16336 : exactInterval 15 16336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16336 : oddCount 16336 15 = 8 ∧ acceleratedOrbit 15 16336 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16336) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16336.1, data_15_16336.2]

/-- Complete interval computation for depth 15, residue 16337. -/
theorem bounds_15_16337 : exactInterval 15 16337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16337 : oddCount 16337 15 = 7 ∧ acceleratedOrbit 15 16337 = 1091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16337) = 3 ^ 7 * m + 1091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16337.1, data_15_16337.2]

/-- Complete interval computation for depth 15, residue 16338. -/
theorem bounds_15_16338 : exactInterval 15 16338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16338 : oddCount 16338 15 = 8 ∧ acceleratedOrbit 15 16338 = 3272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16338) = 3 ^ 8 * m + 3272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16338.1, data_15_16338.2]

/-- Complete interval computation for depth 15, residue 16339. -/
theorem bounds_15_16339 : exactInterval 15 16339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16339 : oddCount 16339 15 = 8 ∧ acceleratedOrbit 15 16339 = 3272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16339) = 3 ^ 8 * m + 3272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16339.1, data_15_16339.2]

/-- Complete interval computation for depth 15, residue 16340. -/
theorem bounds_15_16340 : exactInterval 15 16340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16340 : oddCount 16340 15 = 8 ∧ acceleratedOrbit 15 16340 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16340) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16340.1, data_15_16340.2]

/-- Complete interval computation for depth 15, residue 16341. -/
theorem bounds_15_16341 : exactInterval 15 16341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16341 : oddCount 16341 15 = 8 ∧ acceleratedOrbit 15 16341 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16341) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16341.1, data_15_16341.2]

/-- Complete interval computation for depth 15, residue 16342. -/
theorem bounds_15_16342 : exactInterval 15 16342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16342 : oddCount 16342 15 = 11 ∧ acceleratedOrbit 15 16342 = 88370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16342) = 3 ^ 11 * m + 88370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16342.1, data_15_16342.2]

/-- Complete interval computation for depth 15, residue 16343. -/
theorem bounds_15_16343 : exactInterval 15 16343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16343 : oddCount 16343 15 = 11 ∧ acceleratedOrbit 15 16343 = 88370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16343) = 3 ^ 11 * m + 88370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16343.1, data_15_16343.2]

/-- Complete interval computation for depth 15, residue 16344. -/
theorem bounds_15_16344 : exactInterval 15 16344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16344 : oddCount 16344 15 = 9 ∧ acceleratedOrbit 15 16344 = 9827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16344) = 3 ^ 9 * m + 9827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16344.1, data_15_16344.2]

/-- Complete interval computation for depth 15, residue 16345. -/
theorem bounds_15_16345 : exactInterval 15 16345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16345 : oddCount 16345 15 = 7 ∧ acceleratedOrbit 15 16345 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16345) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16345.1, data_15_16345.2]

/-- Complete interval computation for depth 15, residue 16346. -/
theorem bounds_15_16346 : exactInterval 15 16346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16346 : oddCount 16346 15 = 9 ∧ acceleratedOrbit 15 16346 = 9827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16346) = 3 ^ 9 * m + 9827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16346.1, data_15_16346.2]

/-- Complete interval computation for depth 15, residue 16347. -/
theorem bounds_15_16347 : exactInterval 15 16347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16347 : oddCount 16347 15 = 9 ∧ acceleratedOrbit 15 16347 = 9821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16347) = 3 ^ 9 * m + 9821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16347.1, data_15_16347.2]

/-- Complete interval computation for depth 15, residue 16348. -/
theorem bounds_15_16348 : exactInterval 15 16348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16348 : oddCount 16348 15 = 9 ∧ acceleratedOrbit 15 16348 = 9827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16348) = 3 ^ 9 * m + 9827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16348.1, data_15_16348.2]

/-- Complete interval computation for depth 15, residue 16349. -/
theorem bounds_15_16349 : exactInterval 15 16349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16349 : oddCount 16349 15 = 9 ∧ acceleratedOrbit 15 16349 = 9827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16349) = 3 ^ 9 * m + 9827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16349.1, data_15_16349.2]

/-- Complete interval computation for depth 15, residue 16350. -/
theorem bounds_15_16350 : exactInterval 15 16350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16350 : oddCount 16350 15 = 9 ∧ acceleratedOrbit 15 16350 = 9823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16350) = 3 ^ 9 * m + 9823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16350.1, data_15_16350.2]

end Collatz.Research.PassageAtlas.Batch0499
