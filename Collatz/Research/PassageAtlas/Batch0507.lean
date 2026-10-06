import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0507

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16580. -/
theorem bounds_15_16580 : exactInterval 15 16580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16580 : oddCount 16580 15 = 7 ∧ acceleratedOrbit 15 16580 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16580) = 3 ^ 7 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16580.1, data_15_16580.2]

/-- Complete interval computation for depth 15, residue 16581. -/
theorem bounds_15_16581 : exactInterval 15 16581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16581 : oddCount 16581 15 = 7 ∧ acceleratedOrbit 15 16581 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16581) = 3 ^ 7 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16581.1, data_15_16581.2]

/-- Complete interval computation for depth 15, residue 16582. -/
theorem bounds_15_16582 : exactInterval 15 16582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16582 : oddCount 16582 15 = 7 ∧ acceleratedOrbit 15 16582 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16582) = 3 ^ 7 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16582.1, data_15_16582.2]

/-- Complete interval computation for depth 15, residue 16583. -/
theorem bounds_15_16583 : exactInterval 15 16583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16583 : oddCount 16583 15 = 11 ∧ acceleratedOrbit 15 16583 = 89666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16583) = 3 ^ 11 * m + 89666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16583.1, data_15_16583.2]

/-- Complete interval computation for depth 15, residue 16584. -/
theorem bounds_15_16584 : exactInterval 15 16584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16584 : oddCount 16584 15 = 7 ∧ acceleratedOrbit 15 16584 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16584) = 3 ^ 7 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16584.1, data_15_16584.2]

/-- Complete interval computation for depth 15, residue 16585. -/
theorem bounds_15_16585 : exactInterval 15 16585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16585 : oddCount 16585 15 = 4 ∧ acceleratedOrbit 15 16585 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16585) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16585.1, data_15_16585.2]

/-- Complete interval computation for depth 15, residue 16586. -/
theorem bounds_15_16586 : exactInterval 15 16586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16586 : oddCount 16586 15 = 7 ∧ acceleratedOrbit 15 16586 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16586) = 3 ^ 7 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16586.1, data_15_16586.2]

/-- Complete interval computation for depth 15, residue 16587. -/
theorem bounds_15_16587 : exactInterval 15 16587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16587 : oddCount 16587 15 = 8 ∧ acceleratedOrbit 15 16587 = 3323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16587) = 3 ^ 8 * m + 3323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16587.1, data_15_16587.2]

/-- Complete interval computation for depth 15, residue 16588. -/
theorem bounds_15_16588 : exactInterval 15 16588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16588 : oddCount 16588 15 = 7 ∧ acceleratedOrbit 15 16588 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16588) = 3 ^ 7 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16588.1, data_15_16588.2]

/-- Complete interval computation for depth 15, residue 16589. -/
theorem bounds_15_16589 : exactInterval 15 16589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16589 : oddCount 16589 15 = 7 ∧ acceleratedOrbit 15 16589 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16589) = 3 ^ 7 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16589.1, data_15_16589.2]

/-- Complete interval computation for depth 15, residue 16590. -/
theorem bounds_15_16590 : exactInterval 15 16590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16590 : oddCount 16590 15 = 9 ∧ acceleratedOrbit 15 16590 = 9967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16590) = 3 ^ 9 * m + 9967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16590.1, data_15_16590.2]

/-- Complete interval computation for depth 15, residue 16591. -/
theorem bounds_15_16591 : exactInterval 15 16591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16591 : oddCount 16591 15 = 9 ∧ acceleratedOrbit 15 16591 = 9967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16591) = 3 ^ 9 * m + 9967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16591.1, data_15_16591.2]

/-- Complete interval computation for depth 15, residue 16592. -/
theorem bounds_15_16592 : exactInterval 15 16592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16592 : oddCount 16592 15 = 5 ∧ acceleratedOrbit 15 16592 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16592) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16592.1, data_15_16592.2]

/-- Complete interval computation for depth 15, residue 16593. -/
theorem bounds_15_16593 : exactInterval 15 16593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16593 : oddCount 16593 15 = 7 ∧ acceleratedOrbit 15 16593 = 1108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16593) = 3 ^ 7 * m + 1108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16593.1, data_15_16593.2]

/-- Complete interval computation for depth 15, residue 16594. -/
theorem bounds_15_16594 : exactInterval 15 16594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16594 : oddCount 16594 15 = 7 ∧ acceleratedOrbit 15 16594 = 1108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16594) = 3 ^ 7 * m + 1108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16594.1, data_15_16594.2]

/-- Complete interval computation for depth 15, residue 16595. -/
theorem bounds_15_16595 : exactInterval 15 16595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16595 : oddCount 16595 15 = 7 ∧ acceleratedOrbit 15 16595 = 1108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16595) = 3 ^ 7 * m + 1108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16595.1, data_15_16595.2]

/-- Complete interval computation for depth 15, residue 16596. -/
theorem bounds_15_16596 : exactInterval 15 16596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16596 : oddCount 16596 15 = 5 ∧ acceleratedOrbit 15 16596 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16596) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16596.1, data_15_16596.2]

/-- Complete interval computation for depth 15, residue 16597. -/
theorem bounds_15_16597 : exactInterval 15 16597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16597 : oddCount 16597 15 = 5 ∧ acceleratedOrbit 15 16597 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16597) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16597.1, data_15_16597.2]

/-- Complete interval computation for depth 15, residue 16598. -/
theorem bounds_15_16598 : exactInterval 15 16598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16598 : oddCount 16598 15 = 9 ∧ acceleratedOrbit 15 16598 = 9973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16598) = 3 ^ 9 * m + 9973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16598.1, data_15_16598.2]

/-- Complete interval computation for depth 15, residue 16599. -/
theorem bounds_15_16599 : exactInterval 15 16599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16599 : oddCount 16599 15 = 9 ∧ acceleratedOrbit 15 16599 = 9973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16599) = 3 ^ 9 * m + 9973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16599.1, data_15_16599.2]

/-- Complete interval computation for depth 15, residue 16600. -/
theorem bounds_15_16600 : exactInterval 15 16600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16600 : oddCount 16600 15 = 8 ∧ acceleratedOrbit 15 16600 = 3326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16600) = 3 ^ 8 * m + 3326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16600.1, data_15_16600.2]

/-- Complete interval computation for depth 15, residue 16601. -/
theorem bounds_15_16601 : exactInterval 15 16601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16601 : oddCount 16601 15 = 7 ∧ acceleratedOrbit 15 16601 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16601) = 3 ^ 7 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16601.1, data_15_16601.2]

/-- Complete interval computation for depth 15, residue 16602. -/
theorem bounds_15_16602 : exactInterval 15 16602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16602 : oddCount 16602 15 = 8 ∧ acceleratedOrbit 15 16602 = 3326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16602) = 3 ^ 8 * m + 3326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16602.1, data_15_16602.2]

/-- Complete interval computation for depth 15, residue 16603. -/
theorem bounds_15_16603 : exactInterval 15 16603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16603 : oddCount 16603 15 = 8 ∧ acceleratedOrbit 15 16603 = 3325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16603) = 3 ^ 8 * m + 3325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16603.1, data_15_16603.2]

/-- Complete interval computation for depth 15, residue 16604. -/
theorem bounds_15_16604 : exactInterval 15 16604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16604 : oddCount 16604 15 = 8 ∧ acceleratedOrbit 15 16604 = 3326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16604) = 3 ^ 8 * m + 3326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16604.1, data_15_16604.2]

/-- Complete interval computation for depth 15, residue 16605. -/
theorem bounds_15_16605 : exactInterval 15 16605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16605 : oddCount 16605 15 = 8 ∧ acceleratedOrbit 15 16605 = 3326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16605) = 3 ^ 8 * m + 3326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16605.1, data_15_16605.2]

/-- Complete interval computation for depth 15, residue 16606. -/
theorem bounds_15_16606 : exactInterval 15 16606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16606 : oddCount 16606 15 = 11 ∧ acceleratedOrbit 15 16606 = 89788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16606) = 3 ^ 11 * m + 89788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16606.1, data_15_16606.2]

/-- Complete interval computation for depth 15, residue 16607. -/
theorem bounds_15_16607 : exactInterval 15 16607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16607 : oddCount 16607 15 = 11 ∧ acceleratedOrbit 15 16607 = 89788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16607) = 3 ^ 11 * m + 89788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16607.1, data_15_16607.2]

/-- Complete interval computation for depth 15, residue 16608. -/
theorem bounds_15_16608 : exactInterval 15 16608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16608 : oddCount 16608 15 = 6 ∧ acceleratedOrbit 15 16608 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16608) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16608.1, data_15_16608.2]

/-- Complete interval computation for depth 15, residue 16609. -/
theorem bounds_15_16609 : exactInterval 15 16609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16609 : oddCount 16609 15 = 11 ∧ acceleratedOrbit 15 16609 = 89804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16609) = 3 ^ 11 * m + 89804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16609.1, data_15_16609.2]

/-- Complete interval computation for depth 15, residue 16610. -/
theorem bounds_15_16610 : exactInterval 15 16610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16610 : oddCount 16610 15 = 5 ∧ acceleratedOrbit 15 16610 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16610) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16610.1, data_15_16610.2]

/-- Complete interval computation for depth 15, residue 16611. -/
theorem bounds_15_16611 : exactInterval 15 16611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16611 : oddCount 16611 15 = 5 ∧ acceleratedOrbit 15 16611 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16611) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16611.1, data_15_16611.2]

/-- Complete interval computation for depth 15, residue 16612. -/
theorem bounds_15_16612 : exactInterval 15 16612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16612 : oddCount 16612 15 = 6 ∧ acceleratedOrbit 15 16612 = 370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16612) = 3 ^ 6 * m + 370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16612.1, data_15_16612.2]

end Collatz.Research.PassageAtlas.Batch0507
