import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0137

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4456. -/
theorem bounds_15_4456 : exactInterval 15 4456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4456 : oddCount 4456 15 = 6 ∧ acceleratedOrbit 15 4456 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4456) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4456.1, data_15_4456.2]

/-- Complete interval computation for depth 15, residue 4457. -/
theorem bounds_15_4457 : exactInterval 15 4457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4457 : oddCount 4457 15 = 7 ∧ acceleratedOrbit 15 4457 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4457) = 3 ^ 7 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4457.1, data_15_4457.2]

/-- Complete interval computation for depth 15, residue 4458. -/
theorem bounds_15_4458 : exactInterval 15 4458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4458 : oddCount 4458 15 = 6 ∧ acceleratedOrbit 15 4458 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4458) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4458.1, data_15_4458.2]

/-- Complete interval computation for depth 15, residue 4459. -/
theorem bounds_15_4459 : exactInterval 15 4459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4459 : oddCount 4459 15 = 7 ∧ acceleratedOrbit 15 4459 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4459) = 3 ^ 7 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4459.1, data_15_4459.2]

/-- Complete interval computation for depth 15, residue 4460. -/
theorem bounds_15_4460 : exactInterval 15 4460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4460 : oddCount 4460 15 = 9 ∧ acceleratedOrbit 15 4460 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4460) = 3 ^ 9 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4460.1, data_15_4460.2]

/-- Complete interval computation for depth 15, residue 4461. -/
theorem bounds_15_4461 : exactInterval 15 4461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4461 : oddCount 4461 15 = 9 ∧ acceleratedOrbit 15 4461 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4461) = 3 ^ 9 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4461.1, data_15_4461.2]

/-- Complete interval computation for depth 15, residue 4462. -/
theorem bounds_15_4462 : exactInterval 15 4462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4462 : oddCount 4462 15 = 9 ∧ acceleratedOrbit 15 4462 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4462) = 3 ^ 9 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4462.1, data_15_4462.2]

/-- Complete interval computation for depth 15, residue 4463. -/
theorem bounds_15_4463 : exactInterval 15 4463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4463 : oddCount 4463 15 = 7 ∧ acceleratedOrbit 15 4463 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4463) = 3 ^ 7 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4463.1, data_15_4463.2]

/-- Complete interval computation for depth 15, residue 4464. -/
theorem bounds_15_4464 : exactInterval 15 4464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4464 : oddCount 4464 15 = 6 ∧ acceleratedOrbit 15 4464 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4464) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4464.1, data_15_4464.2]

/-- Complete interval computation for depth 15, residue 4465. -/
theorem bounds_15_4465 : exactInterval 15 4465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4465 : oddCount 4465 15 = 6 ∧ acceleratedOrbit 15 4465 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4465) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4465.1, data_15_4465.2]

/-- Complete interval computation for depth 15, residue 4466. -/
theorem bounds_15_4466 : exactInterval 15 4466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4466 : oddCount 4466 15 = 7 ∧ acceleratedOrbit 15 4466 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4466) = 3 ^ 7 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4466.1, data_15_4466.2]

/-- Complete interval computation for depth 15, residue 4467. -/
theorem bounds_15_4467 : exactInterval 15 4467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4467 : oddCount 4467 15 = 7 ∧ acceleratedOrbit 15 4467 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4467) = 3 ^ 7 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4467.1, data_15_4467.2]

/-- Complete interval computation for depth 15, residue 4468. -/
theorem bounds_15_4468 : exactInterval 15 4468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4468 : oddCount 4468 15 = 6 ∧ acceleratedOrbit 15 4468 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4468) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4468.1, data_15_4468.2]

/-- Complete interval computation for depth 15, residue 4469. -/
theorem bounds_15_4469 : exactInterval 15 4469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4469 : oddCount 4469 15 = 6 ∧ acceleratedOrbit 15 4469 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4469) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4469.1, data_15_4469.2]

/-- Complete interval computation for depth 15, residue 4470. -/
theorem bounds_15_4470 : exactInterval 15 4470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4470 : oddCount 4470 15 = 8 ∧ acceleratedOrbit 15 4470 = 896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4470) = 3 ^ 8 * m + 896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4470.1, data_15_4470.2]

/-- Complete interval computation for depth 15, residue 4471. -/
theorem bounds_15_4471 : exactInterval 15 4471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4471 : oddCount 4471 15 = 8 ∧ acceleratedOrbit 15 4471 = 896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4471) = 3 ^ 8 * m + 896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4471.1, data_15_4471.2]

/-- Complete interval computation for depth 15, residue 4472. -/
theorem bounds_15_4472 : exactInterval 15 4472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4472 : oddCount 4472 15 = 9 ∧ acceleratedOrbit 15 4472 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4472) = 3 ^ 9 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4472.1, data_15_4472.2]

/-- Complete interval computation for depth 15, residue 4473. -/
theorem bounds_15_4473 : exactInterval 15 4473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4473 : oddCount 4473 15 = 11 ∧ acceleratedOrbit 15 4473 = 24194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4473) = 3 ^ 11 * m + 24194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4473.1, data_15_4473.2]

/-- Complete interval computation for depth 15, residue 4474. -/
theorem bounds_15_4474 : exactInterval 15 4474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4474 : oddCount 4474 15 = 9 ∧ acceleratedOrbit 15 4474 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4474) = 3 ^ 9 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4474.1, data_15_4474.2]

/-- Complete interval computation for depth 15, residue 4475. -/
theorem bounds_15_4475 : exactInterval 15 4475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4475 : oddCount 4475 15 = 9 ∧ acceleratedOrbit 15 4475 = 2690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4475) = 3 ^ 9 * m + 2690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4475.1, data_15_4475.2]

/-- Complete interval computation for depth 15, residue 4476. -/
theorem bounds_15_4476 : exactInterval 15 4476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4476 : oddCount 4476 15 = 9 ∧ acceleratedOrbit 15 4476 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4476) = 3 ^ 9 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4476.1, data_15_4476.2]

/-- Complete interval computation for depth 15, residue 4477. -/
theorem bounds_15_4477 : exactInterval 15 4477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4477 : oddCount 4477 15 = 9 ∧ acceleratedOrbit 15 4477 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4477) = 3 ^ 9 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4477.1, data_15_4477.2]

/-- Complete interval computation for depth 15, residue 4478. -/
theorem bounds_15_4478 : exactInterval 15 4478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4478 : oddCount 4478 15 = 7 ∧ acceleratedOrbit 15 4478 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4478) = 3 ^ 7 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4478.1, data_15_4478.2]

/-- Complete interval computation for depth 15, residue 4479. -/
theorem bounds_15_4479 : exactInterval 15 4479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4479 : oddCount 4479 15 = 7 ∧ acceleratedOrbit 15 4479 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4479) = 3 ^ 7 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4479.1, data_15_4479.2]

/-- Complete interval computation for depth 15, residue 4480. -/
theorem bounds_15_4480 : exactInterval 15 4480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4480 : oddCount 4480 15 = 3 ∧ acceleratedOrbit 15 4480 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4480) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4480.1, data_15_4480.2]

/-- Complete interval computation for depth 15, residue 4481. -/
theorem bounds_15_4481 : exactInterval 15 4481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4481 : oddCount 4481 15 = 6 ∧ acceleratedOrbit 15 4481 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4481) = 3 ^ 6 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4481.1, data_15_4481.2]

/-- Complete interval computation for depth 15, residue 4482. -/
theorem bounds_15_4482 : exactInterval 15 4482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4482 : oddCount 4482 15 = 6 ∧ acceleratedOrbit 15 4482 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4482) = 3 ^ 6 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4482.1, data_15_4482.2]

/-- Complete interval computation for depth 15, residue 4483. -/
theorem bounds_15_4483 : exactInterval 15 4483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4483 : oddCount 4483 15 = 6 ∧ acceleratedOrbit 15 4483 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4483) = 3 ^ 6 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4483.1, data_15_4483.2]

/-- Complete interval computation for depth 15, residue 4484. -/
theorem bounds_15_4484 : exactInterval 15 4484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4484 : oddCount 4484 15 = 6 ∧ acceleratedOrbit 15 4484 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4484) = 3 ^ 6 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4484.1, data_15_4484.2]

/-- Complete interval computation for depth 15, residue 4485. -/
theorem bounds_15_4485 : exactInterval 15 4485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4485 : oddCount 4485 15 = 6 ∧ acceleratedOrbit 15 4485 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4485) = 3 ^ 6 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4485.1, data_15_4485.2]

/-- Complete interval computation for depth 15, residue 4486. -/
theorem bounds_15_4486 : exactInterval 15 4486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4486 : oddCount 4486 15 = 6 ∧ acceleratedOrbit 15 4486 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4486) = 3 ^ 6 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4486.1, data_15_4486.2]

/-- Complete interval computation for depth 15, residue 4487. -/
theorem bounds_15_4487 : exactInterval 15 4487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4487 : oddCount 4487 15 = 6 ∧ acceleratedOrbit 15 4487 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4487) = 3 ^ 6 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4487.1, data_15_4487.2]

/-- Complete interval computation for depth 15, residue 4488. -/
theorem bounds_15_4488 : exactInterval 15 4488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4488 : oddCount 4488 15 = 6 ∧ acceleratedOrbit 15 4488 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4488) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4488.1, data_15_4488.2]

end Collatz.Research.PassageAtlas.Batch0137
