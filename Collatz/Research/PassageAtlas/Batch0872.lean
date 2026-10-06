import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0872

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28540. -/
theorem bounds_15_28540 : exactInterval 15 28540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28540 : oddCount 28540 15 = 9 ∧ acceleratedOrbit 15 28540 = 17147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28540) = 3 ^ 9 * m + 17147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28540.1, data_15_28540.2]

/-- Complete interval computation for depth 15, residue 28541. -/
theorem bounds_15_28541 : exactInterval 15 28541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28541 : oddCount 28541 15 = 9 ∧ acceleratedOrbit 15 28541 = 17147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28541) = 3 ^ 9 * m + 17147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28541.1, data_15_28541.2]

/-- Complete interval computation for depth 15, residue 28542. -/
theorem bounds_15_28542 : exactInterval 15 28542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28542 : oddCount 28542 15 = 9 ∧ acceleratedOrbit 15 28542 = 17146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28542) = 3 ^ 9 * m + 17146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28542.1, data_15_28542.2]

/-- Complete interval computation for depth 15, residue 28543. -/
theorem bounds_15_28543 : exactInterval 15 28543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28543 : oddCount 28543 15 = 9 ∧ acceleratedOrbit 15 28543 = 17146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28543) = 3 ^ 9 * m + 17146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28543.1, data_15_28543.2]

/-- Complete interval computation for depth 15, residue 28544. -/
theorem bounds_15_28544 : exactInterval 15 28544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28544 : oddCount 28544 15 = 6 ∧ acceleratedOrbit 15 28544 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28544) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28544.1, data_15_28544.2]

/-- Complete interval computation for depth 15, residue 28545. -/
theorem bounds_15_28545 : exactInterval 15 28545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28545 : oddCount 28545 15 = 8 ∧ acceleratedOrbit 15 28545 = 5717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28545) = 3 ^ 8 * m + 5717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28545.1, data_15_28545.2]

/-- Complete interval computation for depth 15, residue 28546. -/
theorem bounds_15_28546 : exactInterval 15 28546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28546 : oddCount 28546 15 = 7 ∧ acceleratedOrbit 15 28546 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28546) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28546.1, data_15_28546.2]

/-- Complete interval computation for depth 15, residue 28547. -/
theorem bounds_15_28547 : exactInterval 15 28547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28547 : oddCount 28547 15 = 7 ∧ acceleratedOrbit 15 28547 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28547) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28547.1, data_15_28547.2]

/-- Complete interval computation for depth 15, residue 28548. -/
theorem bounds_15_28548 : exactInterval 15 28548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28548 : oddCount 28548 15 = 7 ∧ acceleratedOrbit 15 28548 = 1906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28548) = 3 ^ 7 * m + 1906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28548.1, data_15_28548.2]

/-- Complete interval computation for depth 15, residue 28549. -/
theorem bounds_15_28549 : exactInterval 15 28549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28549 : oddCount 28549 15 = 7 ∧ acceleratedOrbit 15 28549 = 1906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28549) = 3 ^ 7 * m + 1906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28549.1, data_15_28549.2]

/-- Complete interval computation for depth 15, residue 28550. -/
theorem bounds_15_28550 : exactInterval 15 28550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28550 : oddCount 28550 15 = 7 ∧ acceleratedOrbit 15 28550 = 1906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28550) = 3 ^ 7 * m + 1906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28550.1, data_15_28550.2]

/-- Complete interval computation for depth 15, residue 28551. -/
theorem bounds_15_28551 : exactInterval 15 28551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28551 : oddCount 28551 15 = 7 ∧ acceleratedOrbit 15 28551 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28551) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28551.1, data_15_28551.2]

/-- Complete interval computation for depth 15, residue 28552. -/
theorem bounds_15_28552 : exactInterval 15 28552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28552 : oddCount 28552 15 = 6 ∧ acceleratedOrbit 15 28552 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28552) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28552.1, data_15_28552.2]

/-- Complete interval computation for depth 15, residue 28553. -/
theorem bounds_15_28553 : exactInterval 15 28553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28553 : oddCount 28553 15 = 9 ∧ acceleratedOrbit 15 28553 = 17153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28553) = 3 ^ 9 * m + 17153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28553.1, data_15_28553.2]

/-- Complete interval computation for depth 15, residue 28554. -/
theorem bounds_15_28554 : exactInterval 15 28554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28554 : oddCount 28554 15 = 6 ∧ acceleratedOrbit 15 28554 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28554) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28554.1, data_15_28554.2]

/-- Complete interval computation for depth 15, residue 28555. -/
theorem bounds_15_28555 : exactInterval 15 28555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28555 : oddCount 28555 15 = 7 ∧ acceleratedOrbit 15 28555 = 1906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28555) = 3 ^ 7 * m + 1906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28555.1, data_15_28555.2]

/-- Complete interval computation for depth 15, residue 28556. -/
theorem bounds_15_28556 : exactInterval 15 28556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28556 : oddCount 28556 15 = 6 ∧ acceleratedOrbit 15 28556 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28556) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28556.1, data_15_28556.2]

/-- Complete interval computation for depth 15, residue 28557. -/
theorem bounds_15_28557 : exactInterval 15 28557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28557 : oddCount 28557 15 = 6 ∧ acceleratedOrbit 15 28557 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28557) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28557.1, data_15_28557.2]

/-- Complete interval computation for depth 15, residue 28558. -/
theorem bounds_15_28558 : exactInterval 15 28558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28558 : oddCount 28558 15 = 8 ∧ acceleratedOrbit 15 28558 = 5719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28558) = 3 ^ 8 * m + 5719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28558.1, data_15_28558.2]

/-- Complete interval computation for depth 15, residue 28559. -/
theorem bounds_15_28559 : exactInterval 15 28559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28559 : oddCount 28559 15 = 8 ∧ acceleratedOrbit 15 28559 = 5719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28559) = 3 ^ 8 * m + 5719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28559.1, data_15_28559.2]

/-- Complete interval computation for depth 15, residue 28560. -/
theorem bounds_15_28560 : exactInterval 15 28560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28560 : oddCount 28560 15 = 5 ∧ acceleratedOrbit 15 28560 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28560) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28560.1, data_15_28560.2]

/-- Complete interval computation for depth 15, residue 28561. -/
theorem bounds_15_28561 : exactInterval 15 28561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28561 : oddCount 28561 15 = 9 ∧ acceleratedOrbit 15 28561 = 17162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28561) = 3 ^ 9 * m + 17162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28561.1, data_15_28561.2]

/-- Complete interval computation for depth 15, residue 28562. -/
theorem bounds_15_28562 : exactInterval 15 28562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28562 : oddCount 28562 15 = 9 ∧ acceleratedOrbit 15 28562 = 17162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28562) = 3 ^ 9 * m + 17162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28562.1, data_15_28562.2]

/-- Complete interval computation for depth 15, residue 28563. -/
theorem bounds_15_28563 : exactInterval 15 28563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28563 : oddCount 28563 15 = 9 ∧ acceleratedOrbit 15 28563 = 17162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28563) = 3 ^ 9 * m + 17162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28563.1, data_15_28563.2]

/-- Complete interval computation for depth 15, residue 28564. -/
theorem bounds_15_28564 : exactInterval 15 28564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28564 : oddCount 28564 15 = 5 ∧ acceleratedOrbit 15 28564 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28564) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28564.1, data_15_28564.2]

/-- Complete interval computation for depth 15, residue 28565. -/
theorem bounds_15_28565 : exactInterval 15 28565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28565 : oddCount 28565 15 = 5 ∧ acceleratedOrbit 15 28565 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28565) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28565.1, data_15_28565.2]

/-- Complete interval computation for depth 15, residue 28566. -/
theorem bounds_15_28566 : exactInterval 15 28566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28566 : oddCount 28566 15 = 5 ∧ acceleratedOrbit 15 28566 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28566) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28566.1, data_15_28566.2]

/-- Complete interval computation for depth 15, residue 28567. -/
theorem bounds_15_28567 : exactInterval 15 28567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28567 : oddCount 28567 15 = 5 ∧ acceleratedOrbit 15 28567 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28567) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28567.1, data_15_28567.2]

/-- Complete interval computation for depth 15, residue 28568. -/
theorem bounds_15_28568 : exactInterval 15 28568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28568 : oddCount 28568 15 = 5 ∧ acceleratedOrbit 15 28568 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28568) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28568.1, data_15_28568.2]

/-- Complete interval computation for depth 15, residue 28569. -/
theorem bounds_15_28569 : exactInterval 15 28569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28569 : oddCount 28569 15 = 5 ∧ acceleratedOrbit 15 28569 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28569) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28569.1, data_15_28569.2]

/-- Complete interval computation for depth 15, residue 28570. -/
theorem bounds_15_28570 : exactInterval 15 28570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28570 : oddCount 28570 15 = 5 ∧ acceleratedOrbit 15 28570 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28570) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28570.1, data_15_28570.2]

/-- Complete interval computation for depth 15, residue 28571. -/
theorem bounds_15_28571 : exactInterval 15 28571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28571 : oddCount 28571 15 = 7 ∧ acceleratedOrbit 15 28571 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28571) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28571.1, data_15_28571.2]

/-- Complete interval computation for depth 15, residue 28572. -/
theorem bounds_15_28572 : exactInterval 15 28572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28572 : oddCount 28572 15 = 8 ∧ acceleratedOrbit 15 28572 = 5723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28572) = 3 ^ 8 * m + 5723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28572.1, data_15_28572.2]

end Collatz.Research.PassageAtlas.Batch0872
