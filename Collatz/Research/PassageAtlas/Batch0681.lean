import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0681

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22282. -/
theorem bounds_15_22282 : exactInterval 15 22282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22282 : oddCount 22282 15 = 8 ∧ acceleratedOrbit 15 22282 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22282) = 3 ^ 8 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22282.1, data_15_22282.2]

/-- Complete interval computation for depth 15, residue 22283. -/
theorem bounds_15_22283 : exactInterval 15 22283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22283 : oddCount 22283 15 = 8 ∧ acceleratedOrbit 15 22283 = 4463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22283) = 3 ^ 8 * m + 4463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22283.1, data_15_22283.2]

/-- Complete interval computation for depth 15, residue 22284. -/
theorem bounds_15_22284 : exactInterval 15 22284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22284 : oddCount 22284 15 = 8 ∧ acceleratedOrbit 15 22284 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22284) = 3 ^ 8 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22284.1, data_15_22284.2]

/-- Complete interval computation for depth 15, residue 22285. -/
theorem bounds_15_22285 : exactInterval 15 22285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22285 : oddCount 22285 15 = 8 ∧ acceleratedOrbit 15 22285 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22285) = 3 ^ 8 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22285.1, data_15_22285.2]

/-- Complete interval computation for depth 15, residue 22286. -/
theorem bounds_15_22286 : exactInterval 15 22286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22286 : oddCount 22286 15 = 6 ∧ acceleratedOrbit 15 22286 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22286) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22286.1, data_15_22286.2]

/-- Complete interval computation for depth 15, residue 22287. -/
theorem bounds_15_22287 : exactInterval 15 22287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22287 : oddCount 22287 15 = 6 ∧ acceleratedOrbit 15 22287 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22287) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22287.1, data_15_22287.2]

/-- Complete interval computation for depth 15, residue 22288. -/
theorem bounds_15_22288 : exactInterval 15 22288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22288 : oddCount 22288 15 = 4 ∧ acceleratedOrbit 15 22288 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22288) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22288.1, data_15_22288.2]

/-- Complete interval computation for depth 15, residue 22289. -/
theorem bounds_15_22289 : exactInterval 15 22289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22289 : oddCount 22289 15 = 8 ∧ acceleratedOrbit 15 22289 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22289) = 3 ^ 8 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22289.1, data_15_22289.2]

/-- Complete interval computation for depth 15, residue 22290. -/
theorem bounds_15_22290 : exactInterval 15 22290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22290 : oddCount 22290 15 = 11 ∧ acceleratedOrbit 15 22290 = 120527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22290) = 3 ^ 11 * m + 120527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22290.1, data_15_22290.2]

/-- Complete interval computation for depth 15, residue 22291. -/
theorem bounds_15_22291 : exactInterval 15 22291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22291 : oddCount 22291 15 = 11 ∧ acceleratedOrbit 15 22291 = 120527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22291) = 3 ^ 11 * m + 120527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22291.1, data_15_22291.2]

/-- Complete interval computation for depth 15, residue 22292. -/
theorem bounds_15_22292 : exactInterval 15 22292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22292 : oddCount 22292 15 = 4 ∧ acceleratedOrbit 15 22292 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22292) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22292.1, data_15_22292.2]

/-- Complete interval computation for depth 15, residue 22293. -/
theorem bounds_15_22293 : exactInterval 15 22293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22293 : oddCount 22293 15 = 4 ∧ acceleratedOrbit 15 22293 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22293) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22293.1, data_15_22293.2]

/-- Complete interval computation for depth 15, residue 22294. -/
theorem bounds_15_22294 : exactInterval 15 22294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22294 : oddCount 22294 15 = 8 ∧ acceleratedOrbit 15 22294 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22294) = 3 ^ 8 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22294.1, data_15_22294.2]

/-- Complete interval computation for depth 15, residue 22295. -/
theorem bounds_15_22295 : exactInterval 15 22295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22295 : oddCount 22295 15 = 8 ∧ acceleratedOrbit 15 22295 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22295) = 3 ^ 8 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22295.1, data_15_22295.2]

/-- Complete interval computation for depth 15, residue 22296. -/
theorem bounds_15_22296 : exactInterval 15 22296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22296 : oddCount 22296 15 = 4 ∧ acceleratedOrbit 15 22296 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22296) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22296.1, data_15_22296.2]

/-- Complete interval computation for depth 15, residue 22297. -/
theorem bounds_15_22297 : exactInterval 15 22297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22297 : oddCount 22297 15 = 10 ∧ acceleratedOrbit 15 22297 = 40186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22297) = 3 ^ 10 * m + 40186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22297.1, data_15_22297.2]

/-- Complete interval computation for depth 15, residue 22298. -/
theorem bounds_15_22298 : exactInterval 15 22298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22298 : oddCount 22298 15 = 4 ∧ acceleratedOrbit 15 22298 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22298) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22298.1, data_15_22298.2]

/-- Complete interval computation for depth 15, residue 22299. -/
theorem bounds_15_22299 : exactInterval 15 22299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22299 : oddCount 22299 15 = 12 ∧ acceleratedOrbit 15 22299 = 361675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22299) = 3 ^ 12 * m + 361675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22299.1, data_15_22299.2]

/-- Complete interval computation for depth 15, residue 22300. -/
theorem bounds_15_22300 : exactInterval 15 22300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22300 : oddCount 22300 15 = 7 ∧ acceleratedOrbit 15 22300 = 1489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22300) = 3 ^ 7 * m + 1489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22300.1, data_15_22300.2]

/-- Complete interval computation for depth 15, residue 22301. -/
theorem bounds_15_22301 : exactInterval 15 22301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22301 : oddCount 22301 15 = 7 ∧ acceleratedOrbit 15 22301 = 1489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22301) = 3 ^ 7 * m + 1489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22301.1, data_15_22301.2]

/-- Complete interval computation for depth 15, residue 22302. -/
theorem bounds_15_22302 : exactInterval 15 22302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22302 : oddCount 22302 15 = 7 ∧ acceleratedOrbit 15 22302 = 1489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22302) = 3 ^ 7 * m + 1489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22302.1, data_15_22302.2]

/-- Complete interval computation for depth 15, residue 22303. -/
theorem bounds_15_22303 : exactInterval 15 22303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22303 : oddCount 22303 15 = 8 ∧ acceleratedOrbit 15 22303 = 4466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22303) = 3 ^ 8 * m + 4466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22303.1, data_15_22303.2]

/-- Complete interval computation for depth 15, residue 22304. -/
theorem bounds_15_22304 : exactInterval 15 22304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22304 : oddCount 22304 15 = 5 ∧ acceleratedOrbit 15 22304 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22304) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22304.1, data_15_22304.2]

/-- Complete interval computation for depth 15, residue 22305. -/
theorem bounds_15_22305 : exactInterval 15 22305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22305 : oddCount 22305 15 = 8 ∧ acceleratedOrbit 15 22305 = 4468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22305) = 3 ^ 8 * m + 4468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22305.1, data_15_22305.2]

/-- Complete interval computation for depth 15, residue 22306. -/
theorem bounds_15_22306 : exactInterval 15 22306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22306 : oddCount 22306 15 = 6 ∧ acceleratedOrbit 15 22306 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22306) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22306.1, data_15_22306.2]

/-- Complete interval computation for depth 15, residue 22307. -/
theorem bounds_15_22307 : exactInterval 15 22307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22307 : oddCount 22307 15 = 6 ∧ acceleratedOrbit 15 22307 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22307) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22307.1, data_15_22307.2]

/-- Complete interval computation for depth 15, residue 22308. -/
theorem bounds_15_22308 : exactInterval 15 22308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22308 : oddCount 22308 15 = 6 ∧ acceleratedOrbit 15 22308 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22308) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22308.1, data_15_22308.2]

/-- Complete interval computation for depth 15, residue 22309. -/
theorem bounds_15_22309 : exactInterval 15 22309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22309 : oddCount 22309 15 = 6 ∧ acceleratedOrbit 15 22309 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22309) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22309.1, data_15_22309.2]

/-- Complete interval computation for depth 15, residue 22310. -/
theorem bounds_15_22310 : exactInterval 15 22310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22310 : oddCount 22310 15 = 6 ∧ acceleratedOrbit 15 22310 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22310) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22310.1, data_15_22310.2]

/-- Complete interval computation for depth 15, residue 22311. -/
theorem bounds_15_22311 : exactInterval 15 22311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22311 : oddCount 22311 15 = 9 ∧ acceleratedOrbit 15 22311 = 13403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22311) = 3 ^ 9 * m + 13403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22311.1, data_15_22311.2]

/-- Complete interval computation for depth 15, residue 22312. -/
theorem bounds_15_22312 : exactInterval 15 22312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22312 : oddCount 22312 15 = 5 ∧ acceleratedOrbit 15 22312 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22312) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22312.1, data_15_22312.2]

/-- Complete interval computation for depth 15, residue 22313. -/
theorem bounds_15_22313 : exactInterval 15 22313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22313 : oddCount 22313 15 = 9 ∧ acceleratedOrbit 15 22313 = 13405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22313) = 3 ^ 9 * m + 13405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22313.1, data_15_22313.2]

/-- Complete interval computation for depth 15, residue 22314. -/
theorem bounds_15_22314 : exactInterval 15 22314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22314 : oddCount 22314 15 = 5 ∧ acceleratedOrbit 15 22314 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22314) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22314.1, data_15_22314.2]

end Collatz.Research.PassageAtlas.Batch0681
