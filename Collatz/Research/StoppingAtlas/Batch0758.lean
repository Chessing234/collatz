import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0758

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4459. -/
theorem bounds_13_4459 : exactInterval 13 4459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4459 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4459) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4459 : oddCount 4459 13 = 6 ∧ acceleratedOrbit 13 4459 = 397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4459 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4459) = 3 ^ 6 * m + 397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4459.1, data_13_4459.2]

/-- Complete interval computation for depth 13, residue 4460. -/
theorem bounds_13_4460 : exactInterval 13 4460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4460 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4460) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4460 : oddCount 4460 13 = 8 ∧ acceleratedOrbit 13 4460 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4460 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4460) = 3 ^ 8 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4460.1, data_13_4460.2]

/-- Complete interval computation for depth 13, residue 4461. -/
theorem bounds_13_4461 : exactInterval 13 4461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4461 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4461) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4461 : oddCount 4461 13 = 8 ∧ acceleratedOrbit 13 4461 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4461 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4461) = 3 ^ 8 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4461.1, data_13_4461.2]

/-- Complete interval computation for depth 13, residue 4462. -/
theorem bounds_13_4462 : exactInterval 13 4462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4462 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4462) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4462 : oddCount 4462 13 = 8 ∧ acceleratedOrbit 13 4462 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4462 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4462) = 3 ^ 8 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4462.1, data_13_4462.2]

/-- Complete interval computation for depth 13, residue 4463. -/
theorem bounds_13_4463 : exactInterval 13 4463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4463 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4463) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4463 : oddCount 4463 13 = 7 ∧ acceleratedOrbit 13 4463 = 1192 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4463 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4463) = 3 ^ 7 * m + 1192 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4463.1, data_13_4463.2]

/-- Complete interval computation for depth 13, residue 4464. -/
theorem bounds_13_4464 : exactInterval 13 4464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4464 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4464) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4464 : oddCount 4464 13 = 5 ∧ acceleratedOrbit 13 4464 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4464 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4464) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4464.1, data_13_4464.2]

/-- Complete interval computation for depth 13, residue 4465. -/
theorem bounds_13_4465 : exactInterval 13 4465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4465 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4465) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4465 : oddCount 4465 13 = 5 ∧ acceleratedOrbit 13 4465 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4465 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4465) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4465.1, data_13_4465.2]

/-- Complete interval computation for depth 13, residue 4466. -/
theorem bounds_13_4466 : exactInterval 13 4466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4466 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4466) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4466 : oddCount 4466 13 = 6 ∧ acceleratedOrbit 13 4466 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4466 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4466) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4466.1, data_13_4466.2]

/-- Complete interval computation for depth 13, residue 4467. -/
theorem bounds_13_4467 : exactInterval 13 4467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4467 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4467) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4467 : oddCount 4467 13 = 6 ∧ acceleratedOrbit 13 4467 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4467 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4467) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4467.1, data_13_4467.2]

/-- Complete interval computation for depth 13, residue 4468. -/
theorem bounds_13_4468 : exactInterval 13 4468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4468 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4468) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4468 : oddCount 4468 13 = 5 ∧ acceleratedOrbit 13 4468 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4468 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4468) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4468.1, data_13_4468.2]

/-- Complete interval computation for depth 13, residue 4469. -/
theorem bounds_13_4469 : exactInterval 13 4469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4469 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4469) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4469 : oddCount 4469 13 = 5 ∧ acceleratedOrbit 13 4469 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4469 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4469) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4469.1, data_13_4469.2]

/-- Complete interval computation for depth 13, residue 4470. -/
theorem bounds_13_4470 : exactInterval 13 4470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4470 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4470) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4470 : oddCount 4470 13 = 8 ∧ acceleratedOrbit 13 4470 = 3584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4470 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4470) = 3 ^ 8 * m + 3584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4470.1, data_13_4470.2]

/-- Complete interval computation for depth 13, residue 4471. -/
theorem bounds_13_4471 : exactInterval 13 4471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4471 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4471) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4471 : oddCount 4471 13 = 8 ∧ acceleratedOrbit 13 4471 = 3584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4471 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4471) = 3 ^ 8 * m + 3584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4471.1, data_13_4471.2]

/-- Complete interval computation for depth 13, residue 4472. -/
theorem bounds_13_4472 : exactInterval 13 4472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4472 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4472) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4472 : oddCount 4472 13 = 8 ∧ acceleratedOrbit 13 4472 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4472 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4472) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4472.1, data_13_4472.2]

/-- Complete interval computation for depth 13, residue 4473. -/
theorem bounds_13_4473 : exactInterval 13 4473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4473 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4473) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4473 : oddCount 4473 13 = 10 ∧ acceleratedOrbit 13 4473 = 32258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4473 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4473) = 3 ^ 10 * m + 32258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4473.1, data_13_4473.2]

end Collatz.Research.StoppingAtlas.Batch0758
