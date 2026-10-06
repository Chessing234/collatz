import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0422

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3394. -/
theorem bounds_12_3394 : exactInterval 12 3394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3394 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3394) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3394 : oddCount 3394 12 = 6 ∧ acceleratedOrbit 12 3394 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3394 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3394) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3394.1, data_12_3394.2]

/-- Complete interval computation for depth 12, residue 3395. -/
theorem bounds_12_3395 : exactInterval 12 3395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3395 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3395) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3395 : oddCount 3395 12 = 6 ∧ acceleratedOrbit 12 3395 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3395 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3395) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3395.1, data_12_3395.2]

/-- Complete interval computation for depth 12, residue 3396. -/
theorem bounds_12_3396 : exactInterval 12 3396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3396 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3396) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3396 : oddCount 3396 12 = 6 ∧ acceleratedOrbit 12 3396 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3396 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3396) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3396.1, data_12_3396.2]

/-- Complete interval computation for depth 12, residue 3397. -/
theorem bounds_12_3397 : exactInterval 12 3397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3397 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3397) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3397 : oddCount 3397 12 = 6 ∧ acceleratedOrbit 12 3397 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3397 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3397) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3397.1, data_12_3397.2]

/-- Complete interval computation for depth 12, residue 3398. -/
theorem bounds_12_3398 : exactInterval 12 3398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3398 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3398) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3398 : oddCount 3398 12 = 6 ∧ acceleratedOrbit 12 3398 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3398 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3398) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3398.1, data_12_3398.2]

/-- Complete interval computation for depth 12, residue 3399. -/
theorem bounds_12_3399 : exactInterval 12 3399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3399 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3399) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3399 : oddCount 3399 12 = 8 ∧ acceleratedOrbit 12 3399 = 5447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3399 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3399) = 3 ^ 8 * m + 5447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3399.1, data_12_3399.2]

/-- Complete interval computation for depth 12, residue 3400. -/
theorem bounds_12_3400 : exactInterval 12 3400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3400 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3400) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3400 : oddCount 3400 12 = 7 ∧ acceleratedOrbit 12 3400 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3400 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3400) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3400.1, data_12_3400.2]

/-- Complete interval computation for depth 12, residue 3401. -/
theorem bounds_12_3401 : exactInterval 12 3401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3401 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3401) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3401 : oddCount 3401 12 = 8 ∧ acceleratedOrbit 12 3401 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3401 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3401) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3401.1, data_12_3401.2]

/-- Complete interval computation for depth 12, residue 3402. -/
theorem bounds_12_3402 : exactInterval 12 3402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3402 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3402) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3402 : oddCount 3402 12 = 7 ∧ acceleratedOrbit 12 3402 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3402 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3402) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3402.1, data_12_3402.2]

/-- Complete interval computation for depth 12, residue 3403. -/
theorem bounds_12_3403 : exactInterval 12 3403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3403 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3403) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3403 : oddCount 3403 12 = 6 ∧ acceleratedOrbit 12 3403 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3403 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3403) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3403.1, data_12_3403.2]

/-- Complete interval computation for depth 12, residue 3404. -/
theorem bounds_12_3404 : exactInterval 12 3404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3404 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3404) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3404 : oddCount 3404 12 = 7 ∧ acceleratedOrbit 12 3404 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3404 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3404) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3404.1, data_12_3404.2]

/-- Complete interval computation for depth 12, residue 3405. -/
theorem bounds_12_3405 : exactInterval 12 3405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3405 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3405) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3405 : oddCount 3405 12 = 7 ∧ acceleratedOrbit 12 3405 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3405 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3405) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3405.1, data_12_3405.2]

/-- Complete interval computation for depth 12, residue 3406. -/
theorem bounds_12_3406 : exactInterval 12 3406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3406 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3406) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3406 : oddCount 3406 12 = 7 ∧ acceleratedOrbit 12 3406 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3406 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3406) = 3 ^ 7 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3406.1, data_12_3406.2]

/-- Complete interval computation for depth 12, residue 3407. -/
theorem bounds_12_3407 : exactInterval 12 3407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3407 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3407) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3407 : oddCount 3407 12 = 7 ∧ acceleratedOrbit 12 3407 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3407 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3407) = 3 ^ 7 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3407.1, data_12_3407.2]

/-- Complete interval computation for depth 12, residue 3408. -/
theorem bounds_12_3408 : exactInterval 12 3408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3408 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3408) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3408 : oddCount 3408 12 = 2 ∧ acceleratedOrbit 12 3408 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3408 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3408) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3408.1, data_12_3408.2]

end Collatz.Research.StoppingAtlas.Batch0422
