import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0438

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14319. -/
theorem bounds_15_14319 : exactInterval 15 14319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14319 : oddCount 14319 15 = 9 ∧ acceleratedOrbit 15 14319 = 8603 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14319) = 3 ^ 9 * m + 8603 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14319.1, data_15_14319.2]

/-- Complete interval computation for depth 15, residue 14320. -/
theorem bounds_15_14320 : exactInterval 15 14320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14320 : oddCount 14320 15 = 9 ∧ acceleratedOrbit 15 14320 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14320) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14320.1, data_15_14320.2]

/-- Complete interval computation for depth 15, residue 14321. -/
theorem bounds_15_14321 : exactInterval 15 14321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14321 : oddCount 14321 15 = 9 ∧ acceleratedOrbit 15 14321 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14321) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14321.1, data_15_14321.2]

/-- Complete interval computation for depth 15, residue 14322. -/
theorem bounds_15_14322 : exactInterval 15 14322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14322 : oddCount 14322 15 = 9 ∧ acceleratedOrbit 15 14322 = 8606 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14322) = 3 ^ 9 * m + 8606 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14322.1, data_15_14322.2]

/-- Complete interval computation for depth 15, residue 14323. -/
theorem bounds_15_14323 : exactInterval 15 14323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14323 : oddCount 14323 15 = 9 ∧ acceleratedOrbit 15 14323 = 8606 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14323) = 3 ^ 9 * m + 8606 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14323.1, data_15_14323.2]

/-- Complete interval computation for depth 15, residue 14324. -/
theorem bounds_15_14324 : exactInterval 15 14324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14324 : oddCount 14324 15 = 9 ∧ acceleratedOrbit 15 14324 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14324) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14324.1, data_15_14324.2]

/-- Complete interval computation for depth 15, residue 14325. -/
theorem bounds_15_14325 : exactInterval 15 14325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14325 : oddCount 14325 15 = 9 ∧ acceleratedOrbit 15 14325 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14325) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14325.1, data_15_14325.2]

/-- Complete interval computation for depth 15, residue 14326. -/
theorem bounds_15_14326 : exactInterval 15 14326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14326 : oddCount 14326 15 = 9 ∧ acceleratedOrbit 15 14326 = 8608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14326) = 3 ^ 9 * m + 8608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14326.1, data_15_14326.2]

/-- Complete interval computation for depth 15, residue 14327. -/
theorem bounds_15_14327 : exactInterval 15 14327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14327 : oddCount 14327 15 = 9 ∧ acceleratedOrbit 15 14327 = 8608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14327) = 3 ^ 9 * m + 8608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14327.1, data_15_14327.2]

/-- Complete interval computation for depth 15, residue 14328. -/
theorem bounds_15_14328 : exactInterval 15 14328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14328 : oddCount 14328 15 = 10 ∧ acceleratedOrbit 15 14328 = 25834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14328) = 3 ^ 10 * m + 25834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14328.1, data_15_14328.2]

/-- Complete interval computation for depth 15, residue 14329. -/
theorem bounds_15_14329 : exactInterval 15 14329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14329 : oddCount 14329 15 = 8 ∧ acceleratedOrbit 15 14329 = 2870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14329) = 3 ^ 8 * m + 2870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14329.1, data_15_14329.2]

/-- Complete interval computation for depth 15, residue 14330. -/
theorem bounds_15_14330 : exactInterval 15 14330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14330 : oddCount 14330 15 = 10 ∧ acceleratedOrbit 15 14330 = 25834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14330) = 3 ^ 10 * m + 25834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14330.1, data_15_14330.2]

/-- Complete interval computation for depth 15, residue 14331. -/
theorem bounds_15_14331 : exactInterval 15 14331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14331 : oddCount 14331 15 = 10 ∧ acceleratedOrbit 15 14331 = 25829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14331) = 3 ^ 10 * m + 25829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14331.1, data_15_14331.2]

/-- Complete interval computation for depth 15, residue 14332. -/
theorem bounds_15_14332 : exactInterval 15 14332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14332 : oddCount 14332 15 = 10 ∧ acceleratedOrbit 15 14332 = 25834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14332) = 3 ^ 10 * m + 25834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14332.1, data_15_14332.2]

/-- Complete interval computation for depth 15, residue 14333. -/
theorem bounds_15_14333 : exactInterval 15 14333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14333 : oddCount 14333 15 = 10 ∧ acceleratedOrbit 15 14333 = 25834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14333) = 3 ^ 10 * m + 25834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14333.1, data_15_14333.2]

/-- Complete interval computation for depth 15, residue 14334. -/
theorem bounds_15_14334 : exactInterval 15 14334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14334 : oddCount 14334 15 = 13 ∧ acceleratedOrbit 15 14334 = 697517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14334) = 3 ^ 13 * m + 697517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14334.1, data_15_14334.2]

/-- Complete interval computation for depth 15, residue 14335. -/
theorem bounds_15_14335 : exactInterval 15 14335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14335 : oddCount 14335 15 = 13 ∧ acceleratedOrbit 15 14335 = 697517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14335) = 3 ^ 13 * m + 697517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14335.1, data_15_14335.2]

/-- Complete interval computation for depth 15, residue 14336. -/
theorem bounds_15_14336 : exactInterval 15 14336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14336 : oddCount 14336 15 = 3 ∧ acceleratedOrbit 15 14336 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14336) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14336.1, data_15_14336.2]

/-- Complete interval computation for depth 15, residue 14337. -/
theorem bounds_15_14337 : exactInterval 15 14337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14337 : oddCount 14337 15 = 8 ∧ acceleratedOrbit 15 14337 = 2872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14337) = 3 ^ 8 * m + 2872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14337.1, data_15_14337.2]

/-- Complete interval computation for depth 15, residue 14338. -/
theorem bounds_15_14338 : exactInterval 15 14338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14338 : oddCount 14338 15 = 7 ∧ acceleratedOrbit 15 14338 = 958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14338) = 3 ^ 7 * m + 958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14338.1, data_15_14338.2]

/-- Complete interval computation for depth 15, residue 14339. -/
theorem bounds_15_14339 : exactInterval 15 14339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14339 : oddCount 14339 15 = 7 ∧ acceleratedOrbit 15 14339 = 958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14339) = 3 ^ 7 * m + 958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14339.1, data_15_14339.2]

/-- Complete interval computation for depth 15, residue 14340. -/
theorem bounds_15_14340 : exactInterval 15 14340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14340 : oddCount 14340 15 = 8 ∧ acceleratedOrbit 15 14340 = 2875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14340) = 3 ^ 8 * m + 2875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14340.1, data_15_14340.2]

/-- Complete interval computation for depth 15, residue 14341. -/
theorem bounds_15_14341 : exactInterval 15 14341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14341 : oddCount 14341 15 = 8 ∧ acceleratedOrbit 15 14341 = 2875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14341) = 3 ^ 8 * m + 2875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14341.1, data_15_14341.2]

/-- Complete interval computation for depth 15, residue 14342. -/
theorem bounds_15_14342 : exactInterval 15 14342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14342 : oddCount 14342 15 = 8 ∧ acceleratedOrbit 15 14342 = 2875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14342) = 3 ^ 8 * m + 2875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14342.1, data_15_14342.2]

/-- Complete interval computation for depth 15, residue 14343. -/
theorem bounds_15_14343 : exactInterval 15 14343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14343 : oddCount 14343 15 = 7 ∧ acceleratedOrbit 15 14343 = 958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14343) = 3 ^ 7 * m + 958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14343.1, data_15_14343.2]

/-- Complete interval computation for depth 15, residue 14344. -/
theorem bounds_15_14344 : exactInterval 15 14344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14344 : oddCount 14344 15 = 5 ∧ acceleratedOrbit 15 14344 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14344) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14344.1, data_15_14344.2]

/-- Complete interval computation for depth 15, residue 14345. -/
theorem bounds_15_14345 : exactInterval 15 14345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14345 : oddCount 14345 15 = 8 ∧ acceleratedOrbit 15 14345 = 2873 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14345) = 3 ^ 8 * m + 2873 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14345.1, data_15_14345.2]

/-- Complete interval computation for depth 15, residue 14346. -/
theorem bounds_15_14346 : exactInterval 15 14346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14346 : oddCount 14346 15 = 5 ∧ acceleratedOrbit 15 14346 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14346) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14346.1, data_15_14346.2]

/-- Complete interval computation for depth 15, residue 14347. -/
theorem bounds_15_14347 : exactInterval 15 14347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14347 : oddCount 14347 15 = 8 ∧ acceleratedOrbit 15 14347 = 2875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14347) = 3 ^ 8 * m + 2875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14347.1, data_15_14347.2]

/-- Complete interval computation for depth 15, residue 14348. -/
theorem bounds_15_14348 : exactInterval 15 14348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14348 : oddCount 14348 15 = 5 ∧ acceleratedOrbit 15 14348 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14348) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14348.1, data_15_14348.2]

/-- Complete interval computation for depth 15, residue 14349. -/
theorem bounds_15_14349 : exactInterval 15 14349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14349 : oddCount 14349 15 = 5 ∧ acceleratedOrbit 15 14349 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14349) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14349.1, data_15_14349.2]

/-- Complete interval computation for depth 15, residue 14350. -/
theorem bounds_15_14350 : exactInterval 15 14350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14350 : oddCount 14350 15 = 8 ∧ acceleratedOrbit 15 14350 = 2875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14350) = 3 ^ 8 * m + 2875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14350.1, data_15_14350.2]

/-- Complete interval computation for depth 15, residue 14351. -/
theorem bounds_15_14351 : exactInterval 15 14351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14351 : oddCount 14351 15 = 8 ∧ acceleratedOrbit 15 14351 = 2875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14351) = 3 ^ 8 * m + 2875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14351.1, data_15_14351.2]

end Collatz.Research.PassageAtlas.Batch0438
