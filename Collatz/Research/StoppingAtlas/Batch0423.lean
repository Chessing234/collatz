import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0423

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3409. -/
theorem bounds_12_3409 : exactInterval 12 3409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3409 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3409) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3409 : oddCount 3409 12 = 8 ∧ acceleratedOrbit 12 3409 = 5467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3409 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3409) = 3 ^ 8 * m + 5467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3409.1, data_12_3409.2]

/-- Complete interval computation for depth 12, residue 3410. -/
theorem bounds_12_3410 : exactInterval 12 3410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3410 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3410) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3410 : oddCount 3410 12 = 9 ∧ acceleratedOrbit 12 3410 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3410 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3410) = 3 ^ 9 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3410.1, data_12_3410.2]

/-- Complete interval computation for depth 12, residue 3411. -/
theorem bounds_12_3411 : exactInterval 12 3411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3411 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3411) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3411 : oddCount 3411 12 = 9 ∧ acceleratedOrbit 12 3411 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3411 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3411) = 3 ^ 9 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3411.1, data_12_3411.2]

/-- Complete interval computation for depth 12, residue 3412. -/
theorem bounds_12_3412 : exactInterval 12 3412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3412 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3412) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3412 : oddCount 3412 12 = 2 ∧ acceleratedOrbit 12 3412 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3412 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3412) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3412.1, data_12_3412.2]

/-- Complete interval computation for depth 12, residue 3413. -/
theorem bounds_12_3413 : exactInterval 12 3413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3413 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3413) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3413 : oddCount 3413 12 = 2 ∧ acceleratedOrbit 12 3413 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3413 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3413) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3413.1, data_12_3413.2]

/-- Complete interval computation for depth 12, residue 3414. -/
theorem bounds_12_3414 : exactInterval 12 3414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3414 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3414) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3414 : oddCount 3414 12 = 7 ∧ acceleratedOrbit 12 3414 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3414 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3414) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3414.1, data_12_3414.2]

/-- Complete interval computation for depth 12, residue 3415. -/
theorem bounds_12_3415 : exactInterval 12 3415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3415 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3415) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3415 : oddCount 3415 12 = 7 ∧ acceleratedOrbit 12 3415 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3415 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3415) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3415.1, data_12_3415.2]

/-- Complete interval computation for depth 12, residue 3416. -/
theorem bounds_12_3416 : exactInterval 12 3416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3416 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3416) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3416 : oddCount 3416 12 = 6 ∧ acceleratedOrbit 12 3416 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3416 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3416) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3416.1, data_12_3416.2]

/-- Complete interval computation for depth 12, residue 3417. -/
theorem bounds_12_3417 : exactInterval 12 3417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3417 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3417) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3417 : oddCount 3417 12 = 5 ∧ acceleratedOrbit 12 3417 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3417 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3417) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3417.1, data_12_3417.2]

/-- Complete interval computation for depth 12, residue 3418. -/
theorem bounds_12_3418 : exactInterval 12 3418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3418 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3418) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3418 : oddCount 3418 12 = 6 ∧ acceleratedOrbit 12 3418 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3418 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3418) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3418.1, data_12_3418.2]

/-- Complete interval computation for depth 12, residue 3419. -/
theorem bounds_12_3419 : exactInterval 12 3419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3419 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3419) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3419 : oddCount 3419 12 = 8 ∧ acceleratedOrbit 12 3419 = 5480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3419 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3419) = 3 ^ 8 * m + 5480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3419.1, data_12_3419.2]

/-- Complete interval computation for depth 12, residue 3420. -/
theorem bounds_12_3420 : exactInterval 12 3420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3420 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3420) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3420 : oddCount 3420 12 = 6 ∧ acceleratedOrbit 12 3420 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3420 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3420) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3420.1, data_12_3420.2]

/-- Complete interval computation for depth 12, residue 3421. -/
theorem bounds_12_3421 : exactInterval 12 3421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3421 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3421) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3421 : oddCount 3421 12 = 6 ∧ acceleratedOrbit 12 3421 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3421 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3421) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3421.1, data_12_3421.2]

/-- Complete interval computation for depth 12, residue 3422. -/
theorem bounds_12_3422 : exactInterval 12 3422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3422 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3422) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3422 : oddCount 3422 12 = 7 ∧ acceleratedOrbit 12 3422 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3422 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3422) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3422.1, data_12_3422.2]

/-- Complete interval computation for depth 12, residue 3423. -/
theorem bounds_12_3423 : exactInterval 12 3423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3423 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3423) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3423 : oddCount 3423 12 = 7 ∧ acceleratedOrbit 12 3423 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3423 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3423) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3423.1, data_12_3423.2]

/-- Complete interval computation for depth 12, residue 3424. -/
theorem bounds_12_3424 : exactInterval 12 3424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3424 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3424) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3424 : oddCount 3424 12 = 5 ∧ acceleratedOrbit 12 3424 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3424 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3424) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3424.1, data_12_3424.2]

end Collatz.Research.StoppingAtlas.Batch0423
