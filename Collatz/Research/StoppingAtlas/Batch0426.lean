import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0426

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3456. -/
theorem bounds_12_3456 : exactInterval 12 3456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3456 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3456) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3456 : oddCount 3456 12 = 4 ∧ acceleratedOrbit 12 3456 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3456 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3456) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3456.1, data_12_3456.2]

/-- Complete interval computation for depth 12, residue 3457. -/
theorem bounds_12_3457 : exactInterval 12 3457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3457 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3457) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3457 : oddCount 3457 12 = 6 ∧ acceleratedOrbit 12 3457 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3457 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3457) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3457.1, data_12_3457.2]

/-- Complete interval computation for depth 12, residue 3458. -/
theorem bounds_12_3458 : exactInterval 12 3458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3458 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3458) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3458 : oddCount 3458 12 = 5 ∧ acceleratedOrbit 12 3458 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3458 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3458) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3458.1, data_12_3458.2]

/-- Complete interval computation for depth 12, residue 3459. -/
theorem bounds_12_3459 : exactInterval 12 3459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3459 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3459) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3459 : oddCount 3459 12 = 5 ∧ acceleratedOrbit 12 3459 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3459 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3459) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3459.1, data_12_3459.2]

/-- Complete interval computation for depth 12, residue 3460. -/
theorem bounds_12_3460 : exactInterval 12 3460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3460 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3460) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3460 : oddCount 3460 12 = 7 ∧ acceleratedOrbit 12 3460 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3460 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3460) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3460.1, data_12_3460.2]

/-- Complete interval computation for depth 12, residue 3461. -/
theorem bounds_12_3461 : exactInterval 12 3461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3461 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3461) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3461 : oddCount 3461 12 = 7 ∧ acceleratedOrbit 12 3461 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3461 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3461) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3461.1, data_12_3461.2]

/-- Complete interval computation for depth 12, residue 3462. -/
theorem bounds_12_3462 : exactInterval 12 3462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3462 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3462) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3462 : oddCount 3462 12 = 7 ∧ acceleratedOrbit 12 3462 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3462 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3462) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3462.1, data_12_3462.2]

/-- Complete interval computation for depth 12, residue 3463. -/
theorem bounds_12_3463 : exactInterval 12 3463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3463 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3463) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3463 : oddCount 3463 12 = 5 ∧ acceleratedOrbit 12 3463 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3463 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3463) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3463.1, data_12_3463.2]

/-- Complete interval computation for depth 12, residue 3464. -/
theorem bounds_12_3464 : exactInterval 12 3464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3464 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3464) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3464 : oddCount 3464 12 = 3 ∧ acceleratedOrbit 12 3464 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3464 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3464) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3464.1, data_12_3464.2]

/-- Complete interval computation for depth 12, residue 3465. -/
theorem bounds_12_3465 : exactInterval 12 3465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3465 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3465) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3465 : oddCount 3465 12 = 6 ∧ acceleratedOrbit 12 3465 = 617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3465 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3465) = 3 ^ 6 * m + 617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3465.1, data_12_3465.2]

/-- Complete interval computation for depth 12, residue 3466. -/
theorem bounds_12_3466 : exactInterval 12 3466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3466 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3466) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3466 : oddCount 3466 12 = 3 ∧ acceleratedOrbit 12 3466 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3466 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3466) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3466.1, data_12_3466.2]

/-- Complete interval computation for depth 12, residue 3467. -/
theorem bounds_12_3467 : exactInterval 12 3467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3467 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3467) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3467 : oddCount 3467 12 = 7 ∧ acceleratedOrbit 12 3467 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3467 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3467) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3467.1, data_12_3467.2]

/-- Complete interval computation for depth 12, residue 3468. -/
theorem bounds_12_3468 : exactInterval 12 3468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3468 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3468) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3468 : oddCount 3468 12 = 3 ∧ acceleratedOrbit 12 3468 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3468 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3468) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3468.1, data_12_3468.2]

/-- Complete interval computation for depth 12, residue 3469. -/
theorem bounds_12_3469 : exactInterval 12 3469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3469 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3469) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3469 : oddCount 3469 12 = 3 ∧ acceleratedOrbit 12 3469 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3469 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3469) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3469.1, data_12_3469.2]

/-- Complete interval computation for depth 12, residue 3470. -/
theorem bounds_12_3470 : exactInterval 12 3470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3470 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3470) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3470 : oddCount 3470 12 = 5 ∧ acceleratedOrbit 12 3470 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3470 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3470) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3470.1, data_12_3470.2]

end Collatz.Research.StoppingAtlas.Batch0426
