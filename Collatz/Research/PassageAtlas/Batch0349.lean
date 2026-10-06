import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0349

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11403. -/
theorem bounds_15_11403 : exactInterval 15 11403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11403 : oddCount 11403 15 = 8 ∧ acceleratedOrbit 15 11403 = 2285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11403) = 3 ^ 8 * m + 2285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11403.1, data_15_11403.2]

/-- Complete interval computation for depth 15, residue 11404. -/
theorem bounds_15_11404 : exactInterval 15 11404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11404 : oddCount 11404 15 = 5 ∧ acceleratedOrbit 15 11404 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11404) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11404.1, data_15_11404.2]

/-- Complete interval computation for depth 15, residue 11405. -/
theorem bounds_15_11405 : exactInterval 15 11405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11405 : oddCount 11405 15 = 5 ∧ acceleratedOrbit 15 11405 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11405) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11405.1, data_15_11405.2]

/-- Complete interval computation for depth 15, residue 11406. -/
theorem bounds_15_11406 : exactInterval 15 11406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11406 : oddCount 11406 15 = 8 ∧ acceleratedOrbit 15 11406 = 2285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11406) = 3 ^ 8 * m + 2285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11406.1, data_15_11406.2]

/-- Complete interval computation for depth 15, residue 11407. -/
theorem bounds_15_11407 : exactInterval 15 11407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11407 : oddCount 11407 15 = 8 ∧ acceleratedOrbit 15 11407 = 2285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11407) = 3 ^ 8 * m + 2285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11407.1, data_15_11407.2]

/-- Complete interval computation for depth 15, residue 11408. -/
theorem bounds_15_11408 : exactInterval 15 11408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11408 : oddCount 11408 15 = 5 ∧ acceleratedOrbit 15 11408 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11408) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11408.1, data_15_11408.2]

/-- Complete interval computation for depth 15, residue 11409. -/
theorem bounds_15_11409 : exactInterval 15 11409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11409 : oddCount 11409 15 = 10 ∧ acceleratedOrbit 15 11409 = 20573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11409) = 3 ^ 10 * m + 20573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11409.1, data_15_11409.2]

/-- Complete interval computation for depth 15, residue 11410. -/
theorem bounds_15_11410 : exactInterval 15 11410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11410 : oddCount 11410 15 = 10 ∧ acceleratedOrbit 15 11410 = 20573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11410) = 3 ^ 10 * m + 20573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11410.1, data_15_11410.2]

/-- Complete interval computation for depth 15, residue 11411. -/
theorem bounds_15_11411 : exactInterval 15 11411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11411 : oddCount 11411 15 = 10 ∧ acceleratedOrbit 15 11411 = 20573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11411) = 3 ^ 10 * m + 20573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11411.1, data_15_11411.2]

/-- Complete interval computation for depth 15, residue 11412. -/
theorem bounds_15_11412 : exactInterval 15 11412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11412 : oddCount 11412 15 = 5 ∧ acceleratedOrbit 15 11412 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11412) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11412.1, data_15_11412.2]

/-- Complete interval computation for depth 15, residue 11413. -/
theorem bounds_15_11413 : exactInterval 15 11413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11413 : oddCount 11413 15 = 5 ∧ acceleratedOrbit 15 11413 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11413) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11413.1, data_15_11413.2]

/-- Complete interval computation for depth 15, residue 11414. -/
theorem bounds_15_11414 : exactInterval 15 11414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11414 : oddCount 11414 15 = 5 ∧ acceleratedOrbit 15 11414 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11414) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11414.1, data_15_11414.2]

/-- Complete interval computation for depth 15, residue 11415. -/
theorem bounds_15_11415 : exactInterval 15 11415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11415 : oddCount 11415 15 = 5 ∧ acceleratedOrbit 15 11415 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11415) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11415.1, data_15_11415.2]

/-- Complete interval computation for depth 15, residue 11416. -/
theorem bounds_15_11416 : exactInterval 15 11416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11416 : oddCount 11416 15 = 5 ∧ acceleratedOrbit 15 11416 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11416) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11416.1, data_15_11416.2]

/-- Complete interval computation for depth 15, residue 11417. -/
theorem bounds_15_11417 : exactInterval 15 11417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11417 : oddCount 11417 15 = 8 ∧ acceleratedOrbit 15 11417 = 2288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11417) = 3 ^ 8 * m + 2288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11417.1, data_15_11417.2]

/-- Complete interval computation for depth 15, residue 11418. -/
theorem bounds_15_11418 : exactInterval 15 11418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11418 : oddCount 11418 15 = 5 ∧ acceleratedOrbit 15 11418 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11418) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11418.1, data_15_11418.2]

/-- Complete interval computation for depth 15, residue 11419. -/
theorem bounds_15_11419 : exactInterval 15 11419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11419 : oddCount 11419 15 = 11 ∧ acceleratedOrbit 15 11419 = 61742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11419) = 3 ^ 11 * m + 61742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11419.1, data_15_11419.2]

/-- Complete interval computation for depth 15, residue 11420. -/
theorem bounds_15_11420 : exactInterval 15 11420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11420 : oddCount 11420 15 = 8 ∧ acceleratedOrbit 15 11420 = 2288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11420) = 3 ^ 8 * m + 2288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11420.1, data_15_11420.2]

/-- Complete interval computation for depth 15, residue 11421. -/
theorem bounds_15_11421 : exactInterval 15 11421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11421 : oddCount 11421 15 = 8 ∧ acceleratedOrbit 15 11421 = 2288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11421) = 3 ^ 8 * m + 2288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11421.1, data_15_11421.2]

/-- Complete interval computation for depth 15, residue 11422. -/
theorem bounds_15_11422 : exactInterval 15 11422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11422 : oddCount 11422 15 = 8 ∧ acceleratedOrbit 15 11422 = 2288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11422) = 3 ^ 8 * m + 2288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11422.1, data_15_11422.2]

/-- Complete interval computation for depth 15, residue 11423. -/
theorem bounds_15_11423 : exactInterval 15 11423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11423 : oddCount 11423 15 = 11 ∧ acceleratedOrbit 15 11423 = 61760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11423) = 3 ^ 11 * m + 61760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11423.1, data_15_11423.2]

/-- Complete interval computation for depth 15, residue 11424. -/
theorem bounds_15_11424 : exactInterval 15 11424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11424 : oddCount 11424 15 = 4 ∧ acceleratedOrbit 15 11424 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11424) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11424.1, data_15_11424.2]

/-- Complete interval computation for depth 15, residue 11425. -/
theorem bounds_15_11425 : exactInterval 15 11425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11425 : oddCount 11425 15 = 10 ∧ acceleratedOrbit 15 11425 = 20594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11425) = 3 ^ 10 * m + 20594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11425.1, data_15_11425.2]

/-- Complete interval computation for depth 15, residue 11426. -/
theorem bounds_15_11426 : exactInterval 15 11426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11426 : oddCount 11426 15 = 8 ∧ acceleratedOrbit 15 11426 = 2290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11426) = 3 ^ 8 * m + 2290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11426.1, data_15_11426.2]

/-- Complete interval computation for depth 15, residue 11427. -/
theorem bounds_15_11427 : exactInterval 15 11427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11427 : oddCount 11427 15 = 8 ∧ acceleratedOrbit 15 11427 = 2290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11427) = 3 ^ 8 * m + 2290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11427.1, data_15_11427.2]

/-- Complete interval computation for depth 15, residue 11428. -/
theorem bounds_15_11428 : exactInterval 15 11428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11428 : oddCount 11428 15 = 8 ∧ acceleratedOrbit 15 11428 = 2290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11428) = 3 ^ 8 * m + 2290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11428.1, data_15_11428.2]

/-- Complete interval computation for depth 15, residue 11429. -/
theorem bounds_15_11429 : exactInterval 15 11429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11429 : oddCount 11429 15 = 8 ∧ acceleratedOrbit 15 11429 = 2290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11429) = 3 ^ 8 * m + 2290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11429.1, data_15_11429.2]

/-- Complete interval computation for depth 15, residue 11430. -/
theorem bounds_15_11430 : exactInterval 15 11430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11430 : oddCount 11430 15 = 8 ∧ acceleratedOrbit 15 11430 = 2290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11430) = 3 ^ 8 * m + 2290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11430.1, data_15_11430.2]

/-- Complete interval computation for depth 15, residue 11431. -/
theorem bounds_15_11431 : exactInterval 15 11431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11431 : oddCount 11431 15 = 10 ∧ acceleratedOrbit 15 11431 = 20602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11431) = 3 ^ 10 * m + 20602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11431.1, data_15_11431.2]

/-- Complete interval computation for depth 15, residue 11432. -/
theorem bounds_15_11432 : exactInterval 15 11432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11432 : oddCount 11432 15 = 4 ∧ acceleratedOrbit 15 11432 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11432) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11432.1, data_15_11432.2]

/-- Complete interval computation for depth 15, residue 11433. -/
theorem bounds_15_11433 : exactInterval 15 11433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11433 : oddCount 11433 15 = 9 ∧ acceleratedOrbit 15 11433 = 6869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11433) = 3 ^ 9 * m + 6869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11433.1, data_15_11433.2]

/-- Complete interval computation for depth 15, residue 11434. -/
theorem bounds_15_11434 : exactInterval 15 11434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11434 : oddCount 11434 15 = 4 ∧ acceleratedOrbit 15 11434 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11434) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11434.1, data_15_11434.2]

/-- Complete interval computation for depth 15, residue 11435. -/
theorem bounds_15_11435 : exactInterval 15 11435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11435 : oddCount 11435 15 = 7 ∧ acceleratedOrbit 15 11435 = 764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11435) = 3 ^ 7 * m + 764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11435.1, data_15_11435.2]

end Collatz.Research.PassageAtlas.Batch0349
