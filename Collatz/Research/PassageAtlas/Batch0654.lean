import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0654

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21397. -/
theorem bounds_15_21397 : exactInterval 15 21397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21397 : oddCount 21397 15 = 8 ∧ acceleratedOrbit 15 21397 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21397) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21397.1, data_15_21397.2]

/-- Complete interval computation for depth 15, residue 21398. -/
theorem bounds_15_21398 : exactInterval 15 21398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21398 : oddCount 21398 15 = 7 ∧ acceleratedOrbit 15 21398 = 1430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21398) = 3 ^ 7 * m + 1430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21398.1, data_15_21398.2]

/-- Complete interval computation for depth 15, residue 21399. -/
theorem bounds_15_21399 : exactInterval 15 21399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21399 : oddCount 21399 15 = 7 ∧ acceleratedOrbit 15 21399 = 1430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21399) = 3 ^ 7 * m + 1430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21399.1, data_15_21399.2]

/-- Complete interval computation for depth 15, residue 21400. -/
theorem bounds_15_21400 : exactInterval 15 21400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21400 : oddCount 21400 15 = 8 ∧ acceleratedOrbit 15 21400 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21400) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21400.1, data_15_21400.2]

/-- Complete interval computation for depth 15, residue 21401. -/
theorem bounds_15_21401 : exactInterval 15 21401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21401 : oddCount 21401 15 = 7 ∧ acceleratedOrbit 15 21401 = 1430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21401) = 3 ^ 7 * m + 1430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21401.1, data_15_21401.2]

/-- Complete interval computation for depth 15, residue 21402. -/
theorem bounds_15_21402 : exactInterval 15 21402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21402 : oddCount 21402 15 = 8 ∧ acceleratedOrbit 15 21402 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21402) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21402.1, data_15_21402.2]

/-- Complete interval computation for depth 15, residue 21403. -/
theorem bounds_15_21403 : exactInterval 15 21403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21403 : oddCount 21403 15 = 8 ∧ acceleratedOrbit 15 21403 = 4286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21403) = 3 ^ 8 * m + 4286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21403.1, data_15_21403.2]

/-- Complete interval computation for depth 15, residue 21404. -/
theorem bounds_15_21404 : exactInterval 15 21404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21404 : oddCount 21404 15 = 10 ∧ acceleratedOrbit 15 21404 = 38582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21404) = 3 ^ 10 * m + 38582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21404.1, data_15_21404.2]

/-- Complete interval computation for depth 15, residue 21405. -/
theorem bounds_15_21405 : exactInterval 15 21405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21405 : oddCount 21405 15 = 10 ∧ acceleratedOrbit 15 21405 = 38582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21405) = 3 ^ 10 * m + 38582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21405.1, data_15_21405.2]

/-- Complete interval computation for depth 15, residue 21406. -/
theorem bounds_15_21406 : exactInterval 15 21406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21406 : oddCount 21406 15 = 10 ∧ acceleratedOrbit 15 21406 = 38582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21406) = 3 ^ 10 * m + 38582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21406.1, data_15_21406.2]

/-- Complete interval computation for depth 15, residue 21407. -/
theorem bounds_15_21407 : exactInterval 15 21407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21407 : oddCount 21407 15 = 9 ∧ acceleratedOrbit 15 21407 = 12860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21407) = 3 ^ 9 * m + 12860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21407.1, data_15_21407.2]

/-- Complete interval computation for depth 15, residue 21408. -/
theorem bounds_15_21408 : exactInterval 15 21408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21408 : oddCount 21408 15 = 6 ∧ acceleratedOrbit 15 21408 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21408) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21408.1, data_15_21408.2]

/-- Complete interval computation for depth 15, residue 21409. -/
theorem bounds_15_21409 : exactInterval 15 21409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21409 : oddCount 21409 15 = 8 ∧ acceleratedOrbit 15 21409 = 4288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21409) = 3 ^ 8 * m + 4288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21409.1, data_15_21409.2]

/-- Complete interval computation for depth 15, residue 21410. -/
theorem bounds_15_21410 : exactInterval 15 21410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21410 : oddCount 21410 15 = 8 ∧ acceleratedOrbit 15 21410 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21410) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21410.1, data_15_21410.2]

/-- Complete interval computation for depth 15, residue 21411. -/
theorem bounds_15_21411 : exactInterval 15 21411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21411 : oddCount 21411 15 = 8 ∧ acceleratedOrbit 15 21411 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21411) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21411.1, data_15_21411.2]

/-- Complete interval computation for depth 15, residue 21412. -/
theorem bounds_15_21412 : exactInterval 15 21412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21412 : oddCount 21412 15 = 7 ∧ acceleratedOrbit 15 21412 = 1430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21412) = 3 ^ 7 * m + 1430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21412.1, data_15_21412.2]

/-- Complete interval computation for depth 15, residue 21413. -/
theorem bounds_15_21413 : exactInterval 15 21413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21413 : oddCount 21413 15 = 7 ∧ acceleratedOrbit 15 21413 = 1430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21413) = 3 ^ 7 * m + 1430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21413.1, data_15_21413.2]

/-- Complete interval computation for depth 15, residue 21414. -/
theorem bounds_15_21414 : exactInterval 15 21414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21414 : oddCount 21414 15 = 7 ∧ acceleratedOrbit 15 21414 = 1430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21414) = 3 ^ 7 * m + 1430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21414.1, data_15_21414.2]

/-- Complete interval computation for depth 15, residue 21415. -/
theorem bounds_15_21415 : exactInterval 15 21415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21415 : oddCount 21415 15 = 9 ∧ acceleratedOrbit 15 21415 = 12865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21415) = 3 ^ 9 * m + 12865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21415.1, data_15_21415.2]

/-- Complete interval computation for depth 15, residue 21416. -/
theorem bounds_15_21416 : exactInterval 15 21416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21416 : oddCount 21416 15 = 6 ∧ acceleratedOrbit 15 21416 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21416) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21416.1, data_15_21416.2]

/-- Complete interval computation for depth 15, residue 21417. -/
theorem bounds_15_21417 : exactInterval 15 21417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21417 : oddCount 21417 15 = 11 ∧ acceleratedOrbit 15 21417 = 115793 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21417) = 3 ^ 11 * m + 115793 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21417.1, data_15_21417.2]

/-- Complete interval computation for depth 15, residue 21418. -/
theorem bounds_15_21418 : exactInterval 15 21418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21418 : oddCount 21418 15 = 6 ∧ acceleratedOrbit 15 21418 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21418) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21418.1, data_15_21418.2]

/-- Complete interval computation for depth 15, residue 21419. -/
theorem bounds_15_21419 : exactInterval 15 21419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21419 : oddCount 21419 15 = 9 ∧ acceleratedOrbit 15 21419 = 12869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21419) = 3 ^ 9 * m + 12869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21419.1, data_15_21419.2]

/-- Complete interval computation for depth 15, residue 21420. -/
theorem bounds_15_21420 : exactInterval 15 21420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21420 : oddCount 21420 15 = 9 ∧ acceleratedOrbit 15 21420 = 12872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21420) = 3 ^ 9 * m + 12872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21420.1, data_15_21420.2]

/-- Complete interval computation for depth 15, residue 21421. -/
theorem bounds_15_21421 : exactInterval 15 21421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21421 : oddCount 21421 15 = 9 ∧ acceleratedOrbit 15 21421 = 12872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21421) = 3 ^ 9 * m + 12872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21421.1, data_15_21421.2]

/-- Complete interval computation for depth 15, residue 21422. -/
theorem bounds_15_21422 : exactInterval 15 21422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21422 : oddCount 21422 15 = 9 ∧ acceleratedOrbit 15 21422 = 12872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21422) = 3 ^ 9 * m + 12872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21422.1, data_15_21422.2]

/-- Complete interval computation for depth 15, residue 21423. -/
theorem bounds_15_21423 : exactInterval 15 21423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21423 : oddCount 21423 15 = 8 ∧ acceleratedOrbit 15 21423 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21423) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21423.1, data_15_21423.2]

/-- Complete interval computation for depth 15, residue 21424. -/
theorem bounds_15_21424 : exactInterval 15 21424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21424 : oddCount 21424 15 = 4 ∧ acceleratedOrbit 15 21424 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21424) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21424.1, data_15_21424.2]

/-- Complete interval computation for depth 15, residue 21425. -/
theorem bounds_15_21425 : exactInterval 15 21425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21425 : oddCount 21425 15 = 4 ∧ acceleratedOrbit 15 21425 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21425) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21425.1, data_15_21425.2]

/-- Complete interval computation for depth 15, residue 21426. -/
theorem bounds_15_21426 : exactInterval 15 21426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21426 : oddCount 21426 15 = 4 ∧ acceleratedOrbit 15 21426 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21426) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21426.1, data_15_21426.2]

/-- Complete interval computation for depth 15, residue 21427. -/
theorem bounds_15_21427 : exactInterval 15 21427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21427 : oddCount 21427 15 = 4 ∧ acceleratedOrbit 15 21427 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21427) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21427.1, data_15_21427.2]

/-- Complete interval computation for depth 15, residue 21428. -/
theorem bounds_15_21428 : exactInterval 15 21428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21428 : oddCount 21428 15 = 4 ∧ acceleratedOrbit 15 21428 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21428) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21428.1, data_15_21428.2]

/-- Complete interval computation for depth 15, residue 21429. -/
theorem bounds_15_21429 : exactInterval 15 21429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21429 : oddCount 21429 15 = 4 ∧ acceleratedOrbit 15 21429 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21429) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21429.1, data_15_21429.2]

end Collatz.Research.PassageAtlas.Batch0654
