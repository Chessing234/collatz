import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0229

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7471. -/
theorem bounds_15_7471 : exactInterval 15 7471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7471 : oddCount 7471 15 = 10 ∧ acceleratedOrbit 15 7471 = 13466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7471) = 3 ^ 10 * m + 13466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7471.1, data_15_7471.2]

/-- Complete interval computation for depth 15, residue 7472. -/
theorem bounds_15_7472 : exactInterval 15 7472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7472 : oddCount 7472 15 = 6 ∧ acceleratedOrbit 15 7472 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7472) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7472.1, data_15_7472.2]

/-- Complete interval computation for depth 15, residue 7473. -/
theorem bounds_15_7473 : exactInterval 15 7473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7473 : oddCount 7473 15 = 9 ∧ acceleratedOrbit 15 7473 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7473) = 3 ^ 9 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7473.1, data_15_7473.2]

/-- Complete interval computation for depth 15, residue 7474. -/
theorem bounds_15_7474 : exactInterval 15 7474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7474 : oddCount 7474 15 = 9 ∧ acceleratedOrbit 15 7474 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7474) = 3 ^ 9 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7474.1, data_15_7474.2]

/-- Complete interval computation for depth 15, residue 7475. -/
theorem bounds_15_7475 : exactInterval 15 7475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7475 : oddCount 7475 15 = 9 ∧ acceleratedOrbit 15 7475 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7475) = 3 ^ 9 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7475.1, data_15_7475.2]

/-- Complete interval computation for depth 15, residue 7476. -/
theorem bounds_15_7476 : exactInterval 15 7476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7476 : oddCount 7476 15 = 6 ∧ acceleratedOrbit 15 7476 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7476) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7476.1, data_15_7476.2]

/-- Complete interval computation for depth 15, residue 7477. -/
theorem bounds_15_7477 : exactInterval 15 7477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7477 : oddCount 7477 15 = 6 ∧ acceleratedOrbit 15 7477 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7477) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7477.1, data_15_7477.2]

/-- Complete interval computation for depth 15, residue 7478. -/
theorem bounds_15_7478 : exactInterval 15 7478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7478 : oddCount 7478 15 = 11 ∧ acceleratedOrbit 15 7478 = 40445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7478) = 3 ^ 11 * m + 40445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7478.1, data_15_7478.2]

/-- Complete interval computation for depth 15, residue 7479. -/
theorem bounds_15_7479 : exactInterval 15 7479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7479 : oddCount 7479 15 = 11 ∧ acceleratedOrbit 15 7479 = 40445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7479) = 3 ^ 11 * m + 40445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7479.1, data_15_7479.2]

/-- Complete interval computation for depth 15, residue 7480. -/
theorem bounds_15_7480 : exactInterval 15 7480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7480 : oddCount 7480 15 = 7 ∧ acceleratedOrbit 15 7480 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7480) = 3 ^ 7 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7480.1, data_15_7480.2]

/-- Complete interval computation for depth 15, residue 7481. -/
theorem bounds_15_7481 : exactInterval 15 7481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7481 : oddCount 7481 15 = 11 ∧ acceleratedOrbit 15 7481 = 40459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7481) = 3 ^ 11 * m + 40459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7481.1, data_15_7481.2]

/-- Complete interval computation for depth 15, residue 7482. -/
theorem bounds_15_7482 : exactInterval 15 7482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7482 : oddCount 7482 15 = 7 ∧ acceleratedOrbit 15 7482 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7482) = 3 ^ 7 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7482.1, data_15_7482.2]

/-- Complete interval computation for depth 15, residue 7483. -/
theorem bounds_15_7483 : exactInterval 15 7483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7483 : oddCount 7483 15 = 5 ∧ acceleratedOrbit 15 7483 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7483) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7483.1, data_15_7483.2]

/-- Complete interval computation for depth 15, residue 7484. -/
theorem bounds_15_7484 : exactInterval 15 7484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7484 : oddCount 7484 15 = 7 ∧ acceleratedOrbit 15 7484 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7484) = 3 ^ 7 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7484.1, data_15_7484.2]

/-- Complete interval computation for depth 15, residue 7485. -/
theorem bounds_15_7485 : exactInterval 15 7485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7485 : oddCount 7485 15 = 7 ∧ acceleratedOrbit 15 7485 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7485) = 3 ^ 7 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7485.1, data_15_7485.2]

/-- Complete interval computation for depth 15, residue 7486. -/
theorem bounds_15_7486 : exactInterval 15 7486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7486 : oddCount 7486 15 = 9 ∧ acceleratedOrbit 15 7486 = 4498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7486) = 3 ^ 9 * m + 4498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7486.1, data_15_7486.2]

/-- Complete interval computation for depth 15, residue 7487. -/
theorem bounds_15_7487 : exactInterval 15 7487 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7487) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7487 : oddCount 7487 15 = 9 ∧ acceleratedOrbit 15 7487 = 4498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7487) = 3 ^ 9 * m + 4498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7487.1, data_15_7487.2]

/-- Complete interval computation for depth 15, residue 7488. -/
theorem bounds_15_7488 : exactInterval 15 7488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7488 : oddCount 7488 15 = 4 ∧ acceleratedOrbit 15 7488 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7488) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7488.1, data_15_7488.2]

/-- Complete interval computation for depth 15, residue 7489. -/
theorem bounds_15_7489 : exactInterval 15 7489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7489 : oddCount 7489 15 = 6 ∧ acceleratedOrbit 15 7489 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7489) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7489.1, data_15_7489.2]

/-- Complete interval computation for depth 15, residue 7490. -/
theorem bounds_15_7490 : exactInterval 15 7490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7490 : oddCount 7490 15 = 8 ∧ acceleratedOrbit 15 7490 = 1502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7490) = 3 ^ 8 * m + 1502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7490.1, data_15_7490.2]

/-- Complete interval computation for depth 15, residue 7491. -/
theorem bounds_15_7491 : exactInterval 15 7491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7491 : oddCount 7491 15 = 8 ∧ acceleratedOrbit 15 7491 = 1502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7491) = 3 ^ 8 * m + 1502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7491.1, data_15_7491.2]

/-- Complete interval computation for depth 15, residue 7492. -/
theorem bounds_15_7492 : exactInterval 15 7492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7492 : oddCount 7492 15 = 6 ∧ acceleratedOrbit 15 7492 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7492) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7492.1, data_15_7492.2]

/-- Complete interval computation for depth 15, residue 7493. -/
theorem bounds_15_7493 : exactInterval 15 7493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7493 : oddCount 7493 15 = 6 ∧ acceleratedOrbit 15 7493 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7493) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7493.1, data_15_7493.2]

/-- Complete interval computation for depth 15, residue 7494. -/
theorem bounds_15_7494 : exactInterval 15 7494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7494 : oddCount 7494 15 = 6 ∧ acceleratedOrbit 15 7494 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7494) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7494.1, data_15_7494.2]

/-- Complete interval computation for depth 15, residue 7495. -/
theorem bounds_15_7495 : exactInterval 15 7495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7495 : oddCount 7495 15 = 8 ∧ acceleratedOrbit 15 7495 = 1501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7495) = 3 ^ 8 * m + 1501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7495.1, data_15_7495.2]

/-- Complete interval computation for depth 15, residue 7496. -/
theorem bounds_15_7496 : exactInterval 15 7496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7496 : oddCount 7496 15 = 9 ∧ acceleratedOrbit 15 7496 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7496) = 3 ^ 9 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7496.1, data_15_7496.2]

/-- Complete interval computation for depth 15, residue 7497. -/
theorem bounds_15_7497 : exactInterval 15 7497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7497 : oddCount 7497 15 = 10 ∧ acceleratedOrbit 15 7497 = 13517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7497) = 3 ^ 10 * m + 13517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7497.1, data_15_7497.2]

/-- Complete interval computation for depth 15, residue 7498. -/
theorem bounds_15_7498 : exactInterval 15 7498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7498 : oddCount 7498 15 = 9 ∧ acceleratedOrbit 15 7498 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7498) = 3 ^ 9 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7498.1, data_15_7498.2]

/-- Complete interval computation for depth 15, residue 7499. -/
theorem bounds_15_7499 : exactInterval 15 7499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7499 : oddCount 7499 15 = 6 ∧ acceleratedOrbit 15 7499 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7499) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7499.1, data_15_7499.2]

/-- Complete interval computation for depth 15, residue 7500. -/
theorem bounds_15_7500 : exactInterval 15 7500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7500 : oddCount 7500 15 = 9 ∧ acceleratedOrbit 15 7500 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7500) = 3 ^ 9 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7500.1, data_15_7500.2]

/-- Complete interval computation for depth 15, residue 7501. -/
theorem bounds_15_7501 : exactInterval 15 7501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7501 : oddCount 7501 15 = 9 ∧ acceleratedOrbit 15 7501 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7501) = 3 ^ 9 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7501.1, data_15_7501.2]

/-- Complete interval computation for depth 15, residue 7502. -/
theorem bounds_15_7502 : exactInterval 15 7502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7502 : oddCount 7502 15 = 10 ∧ acceleratedOrbit 15 7502 = 13526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7502) = 3 ^ 10 * m + 13526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7502.1, data_15_7502.2]

end Collatz.Research.PassageAtlas.Batch0229
