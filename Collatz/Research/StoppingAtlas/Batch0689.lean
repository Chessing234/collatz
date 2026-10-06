import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0689

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3399. -/
theorem bounds_13_3399 : exactInterval 13 3399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3399 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3399) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3399 : oddCount 3399 13 = 9 ∧ acceleratedOrbit 13 3399 = 8171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3399 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3399) = 3 ^ 9 * m + 8171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3399.1, data_13_3399.2]

/-- Complete interval computation for depth 13, residue 3400. -/
theorem bounds_13_3400 : exactInterval 13 3400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3400 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3400) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3400 : oddCount 3400 13 = 7 ∧ acceleratedOrbit 13 3400 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3400 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3400) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3400.1, data_13_3400.2]

/-- Complete interval computation for depth 13, residue 3401. -/
theorem bounds_13_3401 : exactInterval 13 3401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3401 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3401) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3401 : oddCount 3401 13 = 9 ∧ acceleratedOrbit 13 3401 = 8180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3401 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3401) = 3 ^ 9 * m + 8180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3401.1, data_13_3401.2]

/-- Complete interval computation for depth 13, residue 3402. -/
theorem bounds_13_3402 : exactInterval 13 3402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3402 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3402) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3402 : oddCount 3402 13 = 7 ∧ acceleratedOrbit 13 3402 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3402 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3402) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3402.1, data_13_3402.2]

/-- Complete interval computation for depth 13, residue 3403. -/
theorem bounds_13_3403 : exactInterval 13 3403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3403 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3403) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3403 : oddCount 3403 13 = 7 ∧ acceleratedOrbit 13 3403 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3403 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3403) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3403.1, data_13_3403.2]

/-- Complete interval computation for depth 13, residue 3404. -/
theorem bounds_13_3404 : exactInterval 13 3404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3404 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3404) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3404 : oddCount 3404 13 = 7 ∧ acceleratedOrbit 13 3404 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3404 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3404) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3404.1, data_13_3404.2]

/-- Complete interval computation for depth 13, residue 3405. -/
theorem bounds_13_3405 : exactInterval 13 3405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3405 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3405) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3405 : oddCount 3405 13 = 7 ∧ acceleratedOrbit 13 3405 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3405 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3405) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3405.1, data_13_3405.2]

/-- Complete interval computation for depth 13, residue 3406. -/
theorem bounds_13_3406 : exactInterval 13 3406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3406 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3406) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3406 : oddCount 3406 13 = 7 ∧ acceleratedOrbit 13 3406 = 910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3406 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3406) = 3 ^ 7 * m + 910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3406.1, data_13_3406.2]

/-- Complete interval computation for depth 13, residue 3407. -/
theorem bounds_13_3407 : exactInterval 13 3407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3407 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3407) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3407 : oddCount 3407 13 = 7 ∧ acceleratedOrbit 13 3407 = 910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3407 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3407) = 3 ^ 7 * m + 910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3407.1, data_13_3407.2]

/-- Complete interval computation for depth 13, residue 3408. -/
theorem bounds_13_3408 : exactInterval 13 3408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3408 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3408) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3408 : oddCount 3408 13 = 2 ∧ acceleratedOrbit 13 3408 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3408 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3408) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3408.1, data_13_3408.2]

/-- Complete interval computation for depth 13, residue 3409. -/
theorem bounds_13_3409 : exactInterval 13 3409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3409 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3409) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3409 : oddCount 3409 13 = 9 ∧ acceleratedOrbit 13 3409 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3409 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3409) = 3 ^ 9 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3409.1, data_13_3409.2]

/-- Complete interval computation for depth 13, residue 3410. -/
theorem bounds_13_3410 : exactInterval 13 3410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3410 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3410) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3410 : oddCount 3410 13 = 9 ∧ acceleratedOrbit 13 3410 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3410 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3410) = 3 ^ 9 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3410.1, data_13_3410.2]

/-- Complete interval computation for depth 13, residue 3411. -/
theorem bounds_13_3411 : exactInterval 13 3411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3411 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3411) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3411 : oddCount 3411 13 = 9 ∧ acceleratedOrbit 13 3411 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3411 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3411) = 3 ^ 9 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3411.1, data_13_3411.2]

/-- Complete interval computation for depth 13, residue 3412. -/
theorem bounds_13_3412 : exactInterval 13 3412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3412 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3412) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3412 : oddCount 3412 13 = 2 ∧ acceleratedOrbit 13 3412 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3412 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3412) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3412.1, data_13_3412.2]

/-- Complete interval computation for depth 13, residue 3413. -/
theorem bounds_13_3413 : exactInterval 13 3413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3413 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3413) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3413 : oddCount 3413 13 = 2 ∧ acceleratedOrbit 13 3413 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3413 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3413) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3413.1, data_13_3413.2]

/-- Complete interval computation for depth 13, residue 3414. -/
theorem bounds_13_3414 : exactInterval 13 3414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3414 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3414) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3414 : oddCount 3414 13 = 7 ∧ acceleratedOrbit 13 3414 = 913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3414 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3414) = 3 ^ 7 * m + 913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3414.1, data_13_3414.2]

end Collatz.Research.StoppingAtlas.Batch0689
