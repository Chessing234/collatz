import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0105

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3407. -/
theorem bounds_15_3407 : exactInterval 15 3407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3407 : oddCount 3407 15 = 8 ∧ acceleratedOrbit 15 3407 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3407) = 3 ^ 8 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3407.1, data_15_3407.2]

/-- Complete interval computation for depth 15, residue 3408. -/
theorem bounds_15_3408 : exactInterval 15 3408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3408 : oddCount 3408 15 = 2 ∧ acceleratedOrbit 15 3408 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3408) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3408.1, data_15_3408.2]

/-- Complete interval computation for depth 15, residue 3409. -/
theorem bounds_15_3409 : exactInterval 15 3409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3409 : oddCount 3409 15 = 10 ∧ acceleratedOrbit 15 3409 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3409) = 3 ^ 10 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3409.1, data_15_3409.2]

/-- Complete interval computation for depth 15, residue 3410. -/
theorem bounds_15_3410 : exactInterval 15 3410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3410 : oddCount 3410 15 = 10 ∧ acceleratedOrbit 15 3410 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3410) = 3 ^ 10 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3410.1, data_15_3410.2]

/-- Complete interval computation for depth 15, residue 3411. -/
theorem bounds_15_3411 : exactInterval 15 3411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3411 : oddCount 3411 15 = 10 ∧ acceleratedOrbit 15 3411 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3411) = 3 ^ 10 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3411.1, data_15_3411.2]

/-- Complete interval computation for depth 15, residue 3412. -/
theorem bounds_15_3412 : exactInterval 15 3412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3412 : oddCount 3412 15 = 2 ∧ acceleratedOrbit 15 3412 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3412) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3412.1, data_15_3412.2]

/-- Complete interval computation for depth 15, residue 3413. -/
theorem bounds_15_3413 : exactInterval 15 3413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3413 : oddCount 3413 15 = 2 ∧ acceleratedOrbit 15 3413 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3413) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3413.1, data_15_3413.2]

/-- Complete interval computation for depth 15, residue 3414. -/
theorem bounds_15_3414 : exactInterval 15 3414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3414 : oddCount 3414 15 = 8 ∧ acceleratedOrbit 15 3414 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3414) = 3 ^ 8 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3414.1, data_15_3414.2]

/-- Complete interval computation for depth 15, residue 3415. -/
theorem bounds_15_3415 : exactInterval 15 3415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3415 : oddCount 3415 15 = 8 ∧ acceleratedOrbit 15 3415 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3415) = 3 ^ 8 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3415.1, data_15_3415.2]

/-- Complete interval computation for depth 15, residue 3416. -/
theorem bounds_15_3416 : exactInterval 15 3416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3416 : oddCount 3416 15 = 8 ∧ acceleratedOrbit 15 3416 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3416) = 3 ^ 8 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3416.1, data_15_3416.2]

/-- Complete interval computation for depth 15, residue 3417. -/
theorem bounds_15_3417 : exactInterval 15 3417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3417 : oddCount 3417 15 = 7 ∧ acceleratedOrbit 15 3417 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3417) = 3 ^ 7 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3417.1, data_15_3417.2]

/-- Complete interval computation for depth 15, residue 3418. -/
theorem bounds_15_3418 : exactInterval 15 3418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3418 : oddCount 3418 15 = 8 ∧ acceleratedOrbit 15 3418 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3418) = 3 ^ 8 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3418.1, data_15_3418.2]

/-- Complete interval computation for depth 15, residue 3419. -/
theorem bounds_15_3419 : exactInterval 15 3419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3419 : oddCount 3419 15 = 8 ∧ acceleratedOrbit 15 3419 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3419) = 3 ^ 8 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3419.1, data_15_3419.2]

/-- Complete interval computation for depth 15, residue 3420. -/
theorem bounds_15_3420 : exactInterval 15 3420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3420 : oddCount 3420 15 = 8 ∧ acceleratedOrbit 15 3420 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3420) = 3 ^ 8 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3420.1, data_15_3420.2]

/-- Complete interval computation for depth 15, residue 3421. -/
theorem bounds_15_3421 : exactInterval 15 3421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3421 : oddCount 3421 15 = 8 ∧ acceleratedOrbit 15 3421 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3421) = 3 ^ 8 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3421.1, data_15_3421.2]

/-- Complete interval computation for depth 15, residue 3422. -/
theorem bounds_15_3422 : exactInterval 15 3422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3422 : oddCount 3422 15 = 8 ∧ acceleratedOrbit 15 3422 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3422) = 3 ^ 8 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3422.1, data_15_3422.2]

/-- Complete interval computation for depth 15, residue 3423. -/
theorem bounds_15_3423 : exactInterval 15 3423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3423 : oddCount 3423 15 = 8 ∧ acceleratedOrbit 15 3423 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3423) = 3 ^ 8 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3423.1, data_15_3423.2]

/-- Complete interval computation for depth 15, residue 3424. -/
theorem bounds_15_3424 : exactInterval 15 3424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3424 : oddCount 3424 15 = 7 ∧ acceleratedOrbit 15 3424 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3424) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3424.1, data_15_3424.2]

/-- Complete interval computation for depth 15, residue 3425. -/
theorem bounds_15_3425 : exactInterval 15 3425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3425 : oddCount 3425 15 = 7 ∧ acceleratedOrbit 15 3425 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3425) = 3 ^ 7 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3425.1, data_15_3425.2]

/-- Complete interval computation for depth 15, residue 3426. -/
theorem bounds_15_3426 : exactInterval 15 3426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3426 : oddCount 3426 15 = 5 ∧ acceleratedOrbit 15 3426 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3426) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3426.1, data_15_3426.2]

/-- Complete interval computation for depth 15, residue 3427. -/
theorem bounds_15_3427 : exactInterval 15 3427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3427 : oddCount 3427 15 = 5 ∧ acceleratedOrbit 15 3427 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3427) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3427.1, data_15_3427.2]

/-- Complete interval computation for depth 15, residue 3428. -/
theorem bounds_15_3428 : exactInterval 15 3428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3428 : oddCount 3428 15 = 5 ∧ acceleratedOrbit 15 3428 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3428) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3428.1, data_15_3428.2]

/-- Complete interval computation for depth 15, residue 3429. -/
theorem bounds_15_3429 : exactInterval 15 3429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3429 : oddCount 3429 15 = 5 ∧ acceleratedOrbit 15 3429 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3429) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3429.1, data_15_3429.2]

/-- Complete interval computation for depth 15, residue 3430. -/
theorem bounds_15_3430 : exactInterval 15 3430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3430 : oddCount 3430 15 = 5 ∧ acceleratedOrbit 15 3430 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3430) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3430.1, data_15_3430.2]

/-- Complete interval computation for depth 15, residue 3431. -/
theorem bounds_15_3431 : exactInterval 15 3431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3431 : oddCount 3431 15 = 12 ∧ acceleratedOrbit 15 3431 = 55667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3431) = 3 ^ 12 * m + 55667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3431.1, data_15_3431.2]

/-- Complete interval computation for depth 15, residue 3432. -/
theorem bounds_15_3432 : exactInterval 15 3432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3432 : oddCount 3432 15 = 7 ∧ acceleratedOrbit 15 3432 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3432) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3432.1, data_15_3432.2]

/-- Complete interval computation for depth 15, residue 3433. -/
theorem bounds_15_3433 : exactInterval 15 3433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3433 : oddCount 3433 15 = 9 ∧ acceleratedOrbit 15 3433 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3433) = 3 ^ 9 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3433.1, data_15_3433.2]

/-- Complete interval computation for depth 15, residue 3434. -/
theorem bounds_15_3434 : exactInterval 15 3434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3434 : oddCount 3434 15 = 7 ∧ acceleratedOrbit 15 3434 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3434) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3434.1, data_15_3434.2]

/-- Complete interval computation for depth 15, residue 3435. -/
theorem bounds_15_3435 : exactInterval 15 3435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3435 : oddCount 3435 15 = 10 ∧ acceleratedOrbit 15 3435 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3435) = 3 ^ 10 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3435.1, data_15_3435.2]

/-- Complete interval computation for depth 15, residue 3436. -/
theorem bounds_15_3436 : exactInterval 15 3436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3436 : oddCount 3436 15 = 9 ∧ acceleratedOrbit 15 3436 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3436) = 3 ^ 9 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3436.1, data_15_3436.2]

/-- Complete interval computation for depth 15, residue 3437. -/
theorem bounds_15_3437 : exactInterval 15 3437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3437 : oddCount 3437 15 = 9 ∧ acceleratedOrbit 15 3437 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3437) = 3 ^ 9 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3437.1, data_15_3437.2]

/-- Complete interval computation for depth 15, residue 3438. -/
theorem bounds_15_3438 : exactInterval 15 3438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3438 : oddCount 3438 15 = 9 ∧ acceleratedOrbit 15 3438 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3438) = 3 ^ 9 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3438.1, data_15_3438.2]

/-- Complete interval computation for depth 15, residue 3439. -/
theorem bounds_15_3439 : exactInterval 15 3439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3439 : oddCount 3439 15 = 8 ∧ acceleratedOrbit 15 3439 = 689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3439) = 3 ^ 8 * m + 689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3439.1, data_15_3439.2]

end Collatz.Research.PassageAtlas.Batch0105
