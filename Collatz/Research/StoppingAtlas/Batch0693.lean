import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0693

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3461. -/
theorem bounds_13_3461 : exactInterval 13 3461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3461 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3461) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3461 : oddCount 3461 13 = 8 ∧ acceleratedOrbit 13 3461 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3461 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3461) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3461.1, data_13_3461.2]

/-- Complete interval computation for depth 13, residue 3462. -/
theorem bounds_13_3462 : exactInterval 13 3462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3462 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3462) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3462 : oddCount 3462 13 = 8 ∧ acceleratedOrbit 13 3462 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3462 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3462) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3462.1, data_13_3462.2]

/-- Complete interval computation for depth 13, residue 3463. -/
theorem bounds_13_3463 : exactInterval 13 3463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3463 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3463) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3463 : oddCount 3463 13 = 5 ∧ acceleratedOrbit 13 3463 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3463 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3463) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3463.1, data_13_3463.2]

/-- Complete interval computation for depth 13, residue 3464. -/
theorem bounds_13_3464 : exactInterval 13 3464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3464 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3464) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3464 : oddCount 3464 13 = 4 ∧ acceleratedOrbit 13 3464 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3464 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3464) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3464.1, data_13_3464.2]

/-- Complete interval computation for depth 13, residue 3465. -/
theorem bounds_13_3465 : exactInterval 13 3465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3465 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3465) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3465 : oddCount 3465 13 = 7 ∧ acceleratedOrbit 13 3465 = 926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3465 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3465) = 3 ^ 7 * m + 926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3465.1, data_13_3465.2]

/-- Complete interval computation for depth 13, residue 3466. -/
theorem bounds_13_3466 : exactInterval 13 3466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3466 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3466) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3466 : oddCount 3466 13 = 4 ∧ acceleratedOrbit 13 3466 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3466 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3466) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3466.1, data_13_3466.2]

/-- Complete interval computation for depth 13, residue 3467. -/
theorem bounds_13_3467 : exactInterval 13 3467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3467 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3467) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3467 : oddCount 3467 13 = 8 ∧ acceleratedOrbit 13 3467 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3467 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3467) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3467.1, data_13_3467.2]

/-- Complete interval computation for depth 13, residue 3468. -/
theorem bounds_13_3468 : exactInterval 13 3468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3468 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3468) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3468 : oddCount 3468 13 = 4 ∧ acceleratedOrbit 13 3468 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3468 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3468) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3468.1, data_13_3468.2]

/-- Complete interval computation for depth 13, residue 3469. -/
theorem bounds_13_3469 : exactInterval 13 3469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3469 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3469) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3469 : oddCount 3469 13 = 4 ∧ acceleratedOrbit 13 3469 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3469 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3469) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3469.1, data_13_3469.2]

/-- Complete interval computation for depth 13, residue 3470. -/
theorem bounds_13_3470 : exactInterval 13 3470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3470 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3470) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3470 : oddCount 3470 13 = 5 ∧ acceleratedOrbit 13 3470 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3470 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3470) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3470.1, data_13_3470.2]

/-- Complete interval computation for depth 13, residue 3471. -/
theorem bounds_13_3471 : exactInterval 13 3471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3471 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3471) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3471 : oddCount 3471 13 = 5 ∧ acceleratedOrbit 13 3471 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3471 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3471) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3471.1, data_13_3471.2]

/-- Complete interval computation for depth 13, residue 3472. -/
theorem bounds_13_3472 : exactInterval 13 3472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3472 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3472) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3472 : oddCount 3472 13 = 4 ∧ acceleratedOrbit 13 3472 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3472 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3472) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3472.1, data_13_3472.2]

/-- Complete interval computation for depth 13, residue 3473. -/
theorem bounds_13_3473 : exactInterval 13 3473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3473 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3473) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3473 : oddCount 3473 13 = 6 ∧ acceleratedOrbit 13 3473 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3473 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3473) = 3 ^ 6 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3473.1, data_13_3473.2]

/-- Complete interval computation for depth 13, residue 3474. -/
theorem bounds_13_3474 : exactInterval 13 3474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3474 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3474) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3474 : oddCount 3474 13 = 6 ∧ acceleratedOrbit 13 3474 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3474 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3474) = 3 ^ 6 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3474.1, data_13_3474.2]

/-- Complete interval computation for depth 13, residue 3475. -/
theorem bounds_13_3475 : exactInterval 13 3475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3475 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3475) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3475 : oddCount 3475 13 = 6 ∧ acceleratedOrbit 13 3475 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3475 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3475) = 3 ^ 6 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3475.1, data_13_3475.2]

end Collatz.Research.StoppingAtlas.Batch0693
