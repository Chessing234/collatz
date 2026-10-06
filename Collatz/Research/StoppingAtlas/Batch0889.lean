import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0889

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6471. -/
theorem bounds_13_6471 : exactInterval 13 6471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6471 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6471) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6471 : oddCount 6471 13 = 11 ∧ acceleratedOrbit 13 6471 = 139967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6471 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6471) = 3 ^ 11 * m + 139967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6471.1, data_13_6471.2]

/-- Complete interval computation for depth 13, residue 6472. -/
theorem bounds_13_6472 : exactInterval 13 6472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6472 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6472) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6472 : oddCount 6472 13 = 6 ∧ acceleratedOrbit 13 6472 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6472 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6472) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6472.1, data_13_6472.2]

/-- Complete interval computation for depth 13, residue 6473. -/
theorem bounds_13_6473 : exactInterval 13 6473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6473 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6473) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6473 : oddCount 6473 13 = 7 ∧ acceleratedOrbit 13 6473 = 1729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6473 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6473) = 3 ^ 7 * m + 1729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6473.1, data_13_6473.2]

/-- Complete interval computation for depth 13, residue 6474. -/
theorem bounds_13_6474 : exactInterval 13 6474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6474 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6474) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6474 : oddCount 6474 13 = 6 ∧ acceleratedOrbit 13 6474 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6474 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6474) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6474.1, data_13_6474.2]

/-- Complete interval computation for depth 13, residue 6475. -/
theorem bounds_13_6475 : exactInterval 13 6475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6475 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6475) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6475 : oddCount 6475 13 = 6 ∧ acceleratedOrbit 13 6475 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6475 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6475) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6475.1, data_13_6475.2]

/-- Complete interval computation for depth 13, residue 6476. -/
theorem bounds_13_6476 : exactInterval 13 6476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6476 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6476) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6476 : oddCount 6476 13 = 6 ∧ acceleratedOrbit 13 6476 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6476 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6476) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6476.1, data_13_6476.2]

/-- Complete interval computation for depth 13, residue 6477. -/
theorem bounds_13_6477 : exactInterval 13 6477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6477 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6477) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6477 : oddCount 6477 13 = 6 ∧ acceleratedOrbit 13 6477 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6477 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6477) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6477.1, data_13_6477.2]

/-- Complete interval computation for depth 13, residue 6478. -/
theorem bounds_13_6478 : exactInterval 13 6478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6478 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6478) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6478 : oddCount 6478 13 = 9 ∧ acceleratedOrbit 13 6478 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6478 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6478) = 3 ^ 9 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6478.1, data_13_6478.2]

/-- Complete interval computation for depth 13, residue 6479. -/
theorem bounds_13_6479 : exactInterval 13 6479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6479 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6479) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6479 : oddCount 6479 13 = 9 ∧ acceleratedOrbit 13 6479 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6479 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6479) = 3 ^ 9 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6479.1, data_13_6479.2]

/-- Complete interval computation for depth 13, residue 6480. -/
theorem bounds_13_6480 : exactInterval 13 6480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6480 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6480) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6480 : oddCount 6480 13 = 3 ∧ acceleratedOrbit 13 6480 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6480 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6480) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6480.1, data_13_6480.2]

/-- Complete interval computation for depth 13, residue 6481. -/
theorem bounds_13_6481 : exactInterval 13 6481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6481 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6481) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6481 : oddCount 6481 13 = 8 ∧ acceleratedOrbit 13 6481 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6481 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6481) = 3 ^ 8 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6481.1, data_13_6481.2]

/-- Complete interval computation for depth 13, residue 6482. -/
theorem bounds_13_6482 : exactInterval 13 6482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6482 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6482) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6482 : oddCount 6482 13 = 8 ∧ acceleratedOrbit 13 6482 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6482 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6482) = 3 ^ 8 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6482.1, data_13_6482.2]

/-- Complete interval computation for depth 13, residue 6483. -/
theorem bounds_13_6483 : exactInterval 13 6483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6483 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6483) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6483 : oddCount 6483 13 = 8 ∧ acceleratedOrbit 13 6483 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6483 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6483) = 3 ^ 8 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6483.1, data_13_6483.2]

/-- Complete interval computation for depth 13, residue 6484. -/
theorem bounds_13_6484 : exactInterval 13 6484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6484 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6484) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6484 : oddCount 6484 13 = 3 ∧ acceleratedOrbit 13 6484 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6484 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6484) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6484.1, data_13_6484.2]

/-- Complete interval computation for depth 13, residue 6485. -/
theorem bounds_13_6485 : exactInterval 13 6485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6485 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6485) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6485 : oddCount 6485 13 = 3 ∧ acceleratedOrbit 13 6485 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6485 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6485) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6485.1, data_13_6485.2]

/-- Complete interval computation for depth 13, residue 6486. -/
theorem bounds_13_6486 : exactInterval 13 6486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6486 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6486) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6486 : oddCount 6486 13 = 6 ∧ acceleratedOrbit 13 6486 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6486 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6486) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6486.1, data_13_6486.2]

end Collatz.Research.StoppingAtlas.Batch0889
