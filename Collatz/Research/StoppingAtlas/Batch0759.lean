import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0759

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4474. -/
theorem bounds_13_4474 : exactInterval 13 4474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4474 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4474) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4474 : oddCount 4474 13 = 8 ∧ acceleratedOrbit 13 4474 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4474 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4474) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4474.1, data_13_4474.2]

/-- Complete interval computation for depth 13, residue 4475. -/
theorem bounds_13_4475 : exactInterval 13 4475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4475 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4475) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4475 : oddCount 4475 13 = 8 ∧ acceleratedOrbit 13 4475 = 3586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4475 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4475) = 3 ^ 8 * m + 3586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4475.1, data_13_4475.2]

/-- Complete interval computation for depth 13, residue 4476. -/
theorem bounds_13_4476 : exactInterval 13 4476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4476 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4476) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4476 : oddCount 4476 13 = 8 ∧ acceleratedOrbit 13 4476 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4476 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4476) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4476.1, data_13_4476.2]

/-- Complete interval computation for depth 13, residue 4477. -/
theorem bounds_13_4477 : exactInterval 13 4477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4477 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4477) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4477 : oddCount 4477 13 = 8 ∧ acceleratedOrbit 13 4477 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4477 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4477) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4477.1, data_13_4477.2]

/-- Complete interval computation for depth 13, residue 4478. -/
theorem bounds_13_4478 : exactInterval 13 4478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4478 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4478) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4478 : oddCount 4478 13 = 7 ∧ acceleratedOrbit 13 4478 = 1196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4478 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4478) = 3 ^ 7 * m + 1196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4478.1, data_13_4478.2]

/-- Complete interval computation for depth 13, residue 4479. -/
theorem bounds_13_4479 : exactInterval 13 4479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4479 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4479) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4479 : oddCount 4479 13 = 7 ∧ acceleratedOrbit 13 4479 = 1196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4479 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4479) = 3 ^ 7 * m + 1196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4479.1, data_13_4479.2]

/-- Complete interval computation for depth 13, residue 4480. -/
theorem bounds_13_4480 : exactInterval 13 4480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4480 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4480) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4480 : oddCount 4480 13 = 2 ∧ acceleratedOrbit 13 4480 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4480 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4480) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4480.1, data_13_4480.2]

/-- Complete interval computation for depth 13, residue 4481. -/
theorem bounds_13_4481 : exactInterval 13 4481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4481 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4481) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4481 : oddCount 4481 13 = 5 ∧ acceleratedOrbit 13 4481 = 133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4481 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4481) = 3 ^ 5 * m + 133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4481.1, data_13_4481.2]

/-- Complete interval computation for depth 13, residue 4482. -/
theorem bounds_13_4482 : exactInterval 13 4482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4482 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4482) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4482 : oddCount 4482 13 = 6 ∧ acceleratedOrbit 13 4482 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4482 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4482) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4482.1, data_13_4482.2]

/-- Complete interval computation for depth 13, residue 4483. -/
theorem bounds_13_4483 : exactInterval 13 4483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4483 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4483) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4483 : oddCount 4483 13 = 6 ∧ acceleratedOrbit 13 4483 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4483 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4483) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4483.1, data_13_4483.2]

/-- Complete interval computation for depth 13, residue 4484. -/
theorem bounds_13_4484 : exactInterval 13 4484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4484 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4484) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4484 : oddCount 4484 13 = 6 ∧ acceleratedOrbit 13 4484 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4484 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4484) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4484.1, data_13_4484.2]

/-- Complete interval computation for depth 13, residue 4485. -/
theorem bounds_13_4485 : exactInterval 13 4485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4485 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4485) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4485 : oddCount 4485 13 = 6 ∧ acceleratedOrbit 13 4485 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4485 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4485) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4485.1, data_13_4485.2]

/-- Complete interval computation for depth 13, residue 4486. -/
theorem bounds_13_4486 : exactInterval 13 4486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4486 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4486) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4486 : oddCount 4486 13 = 6 ∧ acceleratedOrbit 13 4486 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4486 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4486) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4486.1, data_13_4486.2]

/-- Complete interval computation for depth 13, residue 4487. -/
theorem bounds_13_4487 : exactInterval 13 4487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4487 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4487) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4487 : oddCount 4487 13 = 6 ∧ acceleratedOrbit 13 4487 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4487 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4487) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4487.1, data_13_4487.2]

/-- Complete interval computation for depth 13, residue 4488. -/
theorem bounds_13_4488 : exactInterval 13 4488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4488 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4488) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4488 : oddCount 4488 13 = 6 ∧ acceleratedOrbit 13 4488 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4488 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4488) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4488.1, data_13_4488.2]

/-- Complete interval computation for depth 13, residue 4489. -/
theorem bounds_13_4489 : exactInterval 13 4489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4489 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4489) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4489 : oddCount 4489 13 = 7 ∧ acceleratedOrbit 13 4489 = 1199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4489 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4489) = 3 ^ 7 * m + 1199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4489.1, data_13_4489.2]

end Collatz.Research.StoppingAtlas.Batch0759
