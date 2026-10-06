import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0931

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30474. -/
theorem bounds_15_30474 : exactInterval 15 30474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30474 : oddCount 30474 15 = 7 ∧ acceleratedOrbit 15 30474 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30474) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30474.1, data_15_30474.2]

/-- Complete interval computation for depth 15, residue 30475. -/
theorem bounds_15_30475 : exactInterval 15 30475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30475 : oddCount 30475 15 = 8 ∧ acceleratedOrbit 15 30475 = 6103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30475) = 3 ^ 8 * m + 6103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30475.1, data_15_30475.2]

/-- Complete interval computation for depth 15, residue 30476. -/
theorem bounds_15_30476 : exactInterval 15 30476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30476 : oddCount 30476 15 = 7 ∧ acceleratedOrbit 15 30476 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30476) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30476.1, data_15_30476.2]

/-- Complete interval computation for depth 15, residue 30477. -/
theorem bounds_15_30477 : exactInterval 15 30477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30477 : oddCount 30477 15 = 7 ∧ acceleratedOrbit 15 30477 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30477) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30477.1, data_15_30477.2]

/-- Complete interval computation for depth 15, residue 30478. -/
theorem bounds_15_30478 : exactInterval 15 30478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30478 : oddCount 30478 15 = 7 ∧ acceleratedOrbit 15 30478 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30478) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30478.1, data_15_30478.2]

/-- Complete interval computation for depth 15, residue 30479. -/
theorem bounds_15_30479 : exactInterval 15 30479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30479 : oddCount 30479 15 = 7 ∧ acceleratedOrbit 15 30479 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30479) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30479.1, data_15_30479.2]

/-- Complete interval computation for depth 15, residue 30480. -/
theorem bounds_15_30480 : exactInterval 15 30480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30480 : oddCount 30480 15 = 4 ∧ acceleratedOrbit 15 30480 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30480) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30480.1, data_15_30480.2]

/-- Complete interval computation for depth 15, residue 30481. -/
theorem bounds_15_30481 : exactInterval 15 30481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30481 : oddCount 30481 15 = 7 ∧ acceleratedOrbit 15 30481 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30481) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30481.1, data_15_30481.2]

/-- Complete interval computation for depth 15, residue 30482. -/
theorem bounds_15_30482 : exactInterval 15 30482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30482 : oddCount 30482 15 = 10 ∧ acceleratedOrbit 15 30482 = 54938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30482) = 3 ^ 10 * m + 54938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30482.1, data_15_30482.2]

/-- Complete interval computation for depth 15, residue 30483. -/
theorem bounds_15_30483 : exactInterval 15 30483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30483 : oddCount 30483 15 = 10 ∧ acceleratedOrbit 15 30483 = 54938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30483) = 3 ^ 10 * m + 54938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30483.1, data_15_30483.2]

/-- Complete interval computation for depth 15, residue 30484. -/
theorem bounds_15_30484 : exactInterval 15 30484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30484 : oddCount 30484 15 = 4 ∧ acceleratedOrbit 15 30484 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30484) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30484.1, data_15_30484.2]

/-- Complete interval computation for depth 15, residue 30485. -/
theorem bounds_15_30485 : exactInterval 15 30485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30485 : oddCount 30485 15 = 4 ∧ acceleratedOrbit 15 30485 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30485) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30485.1, data_15_30485.2]

/-- Complete interval computation for depth 15, residue 30486. -/
theorem bounds_15_30486 : exactInterval 15 30486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30486 : oddCount 30486 15 = 9 ∧ acceleratedOrbit 15 30486 = 18316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30486) = 3 ^ 9 * m + 18316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30486.1, data_15_30486.2]

/-- Complete interval computation for depth 15, residue 30487. -/
theorem bounds_15_30487 : exactInterval 15 30487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30487 : oddCount 30487 15 = 9 ∧ acceleratedOrbit 15 30487 = 18316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30487) = 3 ^ 9 * m + 18316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30487.1, data_15_30487.2]

/-- Complete interval computation for depth 15, residue 30488. -/
theorem bounds_15_30488 : exactInterval 15 30488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30488 : oddCount 30488 15 = 4 ∧ acceleratedOrbit 15 30488 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30488) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30488.1, data_15_30488.2]

/-- Complete interval computation for depth 15, residue 30489. -/
theorem bounds_15_30489 : exactInterval 15 30489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30489 : oddCount 30489 15 = 9 ∧ acceleratedOrbit 15 30489 = 18316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30489) = 3 ^ 9 * m + 18316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30489.1, data_15_30489.2]

/-- Complete interval computation for depth 15, residue 30490. -/
theorem bounds_15_30490 : exactInterval 15 30490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30490 : oddCount 30490 15 = 4 ∧ acceleratedOrbit 15 30490 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30490) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30490.1, data_15_30490.2]

/-- Complete interval computation for depth 15, residue 30491. -/
theorem bounds_15_30491 : exactInterval 15 30491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30491 : oddCount 30491 15 = 11 ∧ acceleratedOrbit 15 30491 = 164845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30491) = 3 ^ 11 * m + 164845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30491.1, data_15_30491.2]

/-- Complete interval computation for depth 15, residue 30492. -/
theorem bounds_15_30492 : exactInterval 15 30492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30492 : oddCount 30492 15 = 7 ∧ acceleratedOrbit 15 30492 = 2036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30492) = 3 ^ 7 * m + 2036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30492.1, data_15_30492.2]

/-- Complete interval computation for depth 15, residue 30493. -/
theorem bounds_15_30493 : exactInterval 15 30493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30493 : oddCount 30493 15 = 7 ∧ acceleratedOrbit 15 30493 = 2036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30493) = 3 ^ 7 * m + 2036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30493.1, data_15_30493.2]

/-- Complete interval computation for depth 15, residue 30494. -/
theorem bounds_15_30494 : exactInterval 15 30494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30494 : oddCount 30494 15 = 7 ∧ acceleratedOrbit 15 30494 = 2036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30494) = 3 ^ 7 * m + 2036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30494.1, data_15_30494.2]

/-- Complete interval computation for depth 15, residue 30495. -/
theorem bounds_15_30495 : exactInterval 15 30495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30495 : oddCount 30495 15 = 9 ∧ acceleratedOrbit 15 30495 = 18319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30495) = 3 ^ 9 * m + 18319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30495.1, data_15_30495.2]

/-- Complete interval computation for depth 15, residue 30496. -/
theorem bounds_15_30496 : exactInterval 15 30496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30496 : oddCount 30496 15 = 5 ∧ acceleratedOrbit 15 30496 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30496) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30496.1, data_15_30496.2]

/-- Complete interval computation for depth 15, residue 30497. -/
theorem bounds_15_30497 : exactInterval 15 30497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30497 : oddCount 30497 15 = 7 ∧ acceleratedOrbit 15 30497 = 2036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30497) = 3 ^ 7 * m + 2036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30497.1, data_15_30497.2]

/-- Complete interval computation for depth 15, residue 30498. -/
theorem bounds_15_30498 : exactInterval 15 30498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30498 : oddCount 30498 15 = 6 ∧ acceleratedOrbit 15 30498 = 679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30498) = 3 ^ 6 * m + 679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30498.1, data_15_30498.2]

/-- Complete interval computation for depth 15, residue 30499. -/
theorem bounds_15_30499 : exactInterval 15 30499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30499 : oddCount 30499 15 = 6 ∧ acceleratedOrbit 15 30499 = 679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30499) = 3 ^ 6 * m + 679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30499.1, data_15_30499.2]

/-- Complete interval computation for depth 15, residue 30500. -/
theorem bounds_15_30500 : exactInterval 15 30500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30500 : oddCount 30500 15 = 6 ∧ acceleratedOrbit 15 30500 = 679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30500) = 3 ^ 6 * m + 679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30500.1, data_15_30500.2]

/-- Complete interval computation for depth 15, residue 30501. -/
theorem bounds_15_30501 : exactInterval 15 30501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30501 : oddCount 30501 15 = 6 ∧ acceleratedOrbit 15 30501 = 679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30501) = 3 ^ 6 * m + 679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30501.1, data_15_30501.2]

/-- Complete interval computation for depth 15, residue 30502. -/
theorem bounds_15_30502 : exactInterval 15 30502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30502 : oddCount 30502 15 = 6 ∧ acceleratedOrbit 15 30502 = 679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30502) = 3 ^ 6 * m + 679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30502.1, data_15_30502.2]

/-- Complete interval computation for depth 15, residue 30503. -/
theorem bounds_15_30503 : exactInterval 15 30503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30503 : oddCount 30503 15 = 11 ∧ acceleratedOrbit 15 30503 = 164915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30503) = 3 ^ 11 * m + 164915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30503.1, data_15_30503.2]

/-- Complete interval computation for depth 15, residue 30504. -/
theorem bounds_15_30504 : exactInterval 15 30504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30504 : oddCount 30504 15 = 5 ∧ acceleratedOrbit 15 30504 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30504) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30504.1, data_15_30504.2]

/-- Complete interval computation for depth 15, residue 30505. -/
theorem bounds_15_30505 : exactInterval 15 30505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30505 : oddCount 30505 15 = 9 ∧ acceleratedOrbit 15 30505 = 18326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30505) = 3 ^ 9 * m + 18326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30505.1, data_15_30505.2]

/-- Complete interval computation for depth 15, residue 30506. -/
theorem bounds_15_30506 : exactInterval 15 30506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30506 : oddCount 30506 15 = 5 ∧ acceleratedOrbit 15 30506 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30506) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30506.1, data_15_30506.2]

end Collatz.Research.PassageAtlas.Batch0931
