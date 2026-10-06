import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0682

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22315. -/
theorem bounds_15_22315 : exactInterval 15 22315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22315 : oddCount 22315 15 = 6 ∧ acceleratedOrbit 15 22315 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22315) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22315.1, data_15_22315.2]

/-- Complete interval computation for depth 15, residue 22316. -/
theorem bounds_15_22316 : exactInterval 15 22316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22316 : oddCount 22316 15 = 6 ∧ acceleratedOrbit 15 22316 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22316) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22316.1, data_15_22316.2]

/-- Complete interval computation for depth 15, residue 22317. -/
theorem bounds_15_22317 : exactInterval 15 22317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22317 : oddCount 22317 15 = 6 ∧ acceleratedOrbit 15 22317 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22317) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22317.1, data_15_22317.2]

/-- Complete interval computation for depth 15, residue 22318. -/
theorem bounds_15_22318 : exactInterval 15 22318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22318 : oddCount 22318 15 = 6 ∧ acceleratedOrbit 15 22318 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22318) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22318.1, data_15_22318.2]

/-- Complete interval computation for depth 15, residue 22319. -/
theorem bounds_15_22319 : exactInterval 15 22319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22319 : oddCount 22319 15 = 9 ∧ acceleratedOrbit 15 22319 = 13409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22319) = 3 ^ 9 * m + 13409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22319.1, data_15_22319.2]

/-- Complete interval computation for depth 15, residue 22320. -/
theorem bounds_15_22320 : exactInterval 15 22320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22320 : oddCount 22320 15 = 5 ∧ acceleratedOrbit 15 22320 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22320) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22320.1, data_15_22320.2]

/-- Complete interval computation for depth 15, residue 22321. -/
theorem bounds_15_22321 : exactInterval 15 22321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22321 : oddCount 22321 15 = 6 ∧ acceleratedOrbit 15 22321 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22321) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22321.1, data_15_22321.2]

/-- Complete interval computation for depth 15, residue 22322. -/
theorem bounds_15_22322 : exactInterval 15 22322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22322 : oddCount 22322 15 = 6 ∧ acceleratedOrbit 15 22322 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22322) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22322.1, data_15_22322.2]

/-- Complete interval computation for depth 15, residue 22323. -/
theorem bounds_15_22323 : exactInterval 15 22323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22323 : oddCount 22323 15 = 6 ∧ acceleratedOrbit 15 22323 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22323) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22323.1, data_15_22323.2]

/-- Complete interval computation for depth 15, residue 22324. -/
theorem bounds_15_22324 : exactInterval 15 22324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22324 : oddCount 22324 15 = 5 ∧ acceleratedOrbit 15 22324 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22324) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22324.1, data_15_22324.2]

/-- Complete interval computation for depth 15, residue 22325. -/
theorem bounds_15_22325 : exactInterval 15 22325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22325 : oddCount 22325 15 = 5 ∧ acceleratedOrbit 15 22325 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22325) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22325.1, data_15_22325.2]

/-- Complete interval computation for depth 15, residue 22326. -/
theorem bounds_15_22326 : exactInterval 15 22326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22326 : oddCount 22326 15 = 8 ∧ acceleratedOrbit 15 22326 = 4472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22326) = 3 ^ 8 * m + 4472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22326.1, data_15_22326.2]

/-- Complete interval computation for depth 15, residue 22327. -/
theorem bounds_15_22327 : exactInterval 15 22327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22327 : oddCount 22327 15 = 8 ∧ acceleratedOrbit 15 22327 = 4472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22327) = 3 ^ 8 * m + 4472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22327.1, data_15_22327.2]

/-- Complete interval computation for depth 15, residue 22328. -/
theorem bounds_15_22328 : exactInterval 15 22328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22328 : oddCount 22328 15 = 10 ∧ acceleratedOrbit 15 22328 = 40256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22328) = 3 ^ 10 * m + 40256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22328.1, data_15_22328.2]

/-- Complete interval computation for depth 15, residue 22329. -/
theorem bounds_15_22329 : exactInterval 15 22329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22329 : oddCount 22329 15 = 8 ∧ acceleratedOrbit 15 22329 = 4472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22329) = 3 ^ 8 * m + 4472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22329.1, data_15_22329.2]

/-- Complete interval computation for depth 15, residue 22330. -/
theorem bounds_15_22330 : exactInterval 15 22330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22330 : oddCount 22330 15 = 10 ∧ acceleratedOrbit 15 22330 = 40256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22330) = 3 ^ 10 * m + 40256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22330.1, data_15_22330.2]

/-- Complete interval computation for depth 15, residue 22331. -/
theorem bounds_15_22331 : exactInterval 15 22331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22331 : oddCount 22331 15 = 6 ∧ acceleratedOrbit 15 22331 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22331) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22331.1, data_15_22331.2]

/-- Complete interval computation for depth 15, residue 22332. -/
theorem bounds_15_22332 : exactInterval 15 22332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22332 : oddCount 22332 15 = 10 ∧ acceleratedOrbit 15 22332 = 40256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22332) = 3 ^ 10 * m + 40256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22332.1, data_15_22332.2]

/-- Complete interval computation for depth 15, residue 22333. -/
theorem bounds_15_22333 : exactInterval 15 22333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22333 : oddCount 22333 15 = 10 ∧ acceleratedOrbit 15 22333 = 40256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22333) = 3 ^ 10 * m + 40256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22333.1, data_15_22333.2]

/-- Complete interval computation for depth 15, residue 22334. -/
theorem bounds_15_22334 : exactInterval 15 22334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22334 : oddCount 22334 15 = 9 ∧ acceleratedOrbit 15 22334 = 13418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22334) = 3 ^ 9 * m + 13418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22334.1, data_15_22334.2]

/-- Complete interval computation for depth 15, residue 22335. -/
theorem bounds_15_22335 : exactInterval 15 22335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22335 : oddCount 22335 15 = 9 ∧ acceleratedOrbit 15 22335 = 13418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22335) = 3 ^ 9 * m + 13418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22335.1, data_15_22335.2]

/-- Complete interval computation for depth 15, residue 22336. -/
theorem bounds_15_22336 : exactInterval 15 22336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22336 : oddCount 22336 15 = 4 ∧ acceleratedOrbit 15 22336 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22336) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22336.1, data_15_22336.2]

/-- Complete interval computation for depth 15, residue 22337. -/
theorem bounds_15_22337 : exactInterval 15 22337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22337 : oddCount 22337 15 = 5 ∧ acceleratedOrbit 15 22337 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22337) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22337.1, data_15_22337.2]

/-- Complete interval computation for depth 15, residue 22338. -/
theorem bounds_15_22338 : exactInterval 15 22338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22338 : oddCount 22338 15 = 8 ∧ acceleratedOrbit 15 22338 = 4475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22338) = 3 ^ 8 * m + 4475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22338.1, data_15_22338.2]

/-- Complete interval computation for depth 15, residue 22339. -/
theorem bounds_15_22339 : exactInterval 15 22339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22339 : oddCount 22339 15 = 8 ∧ acceleratedOrbit 15 22339 = 4475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22339) = 3 ^ 8 * m + 4475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22339.1, data_15_22339.2]

/-- Complete interval computation for depth 15, residue 22340. -/
theorem bounds_15_22340 : exactInterval 15 22340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22340 : oddCount 22340 15 = 5 ∧ acceleratedOrbit 15 22340 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22340) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22340.1, data_15_22340.2]

/-- Complete interval computation for depth 15, residue 22341. -/
theorem bounds_15_22341 : exactInterval 15 22341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22341 : oddCount 22341 15 = 5 ∧ acceleratedOrbit 15 22341 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22341) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22341.1, data_15_22341.2]

/-- Complete interval computation for depth 15, residue 22342. -/
theorem bounds_15_22342 : exactInterval 15 22342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22342 : oddCount 22342 15 = 5 ∧ acceleratedOrbit 15 22342 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22342) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22342.1, data_15_22342.2]

/-- Complete interval computation for depth 15, residue 22343. -/
theorem bounds_15_22343 : exactInterval 15 22343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22343 : oddCount 22343 15 = 8 ∧ acceleratedOrbit 15 22343 = 4474 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22343) = 3 ^ 8 * m + 4474 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22343.1, data_15_22343.2]

/-- Complete interval computation for depth 15, residue 22344. -/
theorem bounds_15_22344 : exactInterval 15 22344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22344 : oddCount 22344 15 = 8 ∧ acceleratedOrbit 15 22344 = 4477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22344) = 3 ^ 8 * m + 4477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22344.1, data_15_22344.2]

/-- Complete interval computation for depth 15, residue 22345. -/
theorem bounds_15_22345 : exactInterval 15 22345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22345 : oddCount 22345 15 = 8 ∧ acceleratedOrbit 15 22345 = 4475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22345) = 3 ^ 8 * m + 4475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22345.1, data_15_22345.2]

/-- Complete interval computation for depth 15, residue 22346. -/
theorem bounds_15_22346 : exactInterval 15 22346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22346 : oddCount 22346 15 = 8 ∧ acceleratedOrbit 15 22346 = 4477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22346) = 3 ^ 8 * m + 4477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22346.1, data_15_22346.2]

end Collatz.Research.PassageAtlas.Batch0682
