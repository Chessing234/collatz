import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0721

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23592. -/
theorem bounds_15_23592 : exactInterval 15 23592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23592 : oddCount 23592 15 = 7 ∧ acceleratedOrbit 15 23592 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23592) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23592.1, data_15_23592.2]

/-- Complete interval computation for depth 15, residue 23593. -/
theorem bounds_15_23593 : exactInterval 15 23593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23593 : oddCount 23593 15 = 9 ∧ acceleratedOrbit 15 23593 = 14174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23593) = 3 ^ 9 * m + 14174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23593.1, data_15_23593.2]

/-- Complete interval computation for depth 15, residue 23594. -/
theorem bounds_15_23594 : exactInterval 15 23594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23594 : oddCount 23594 15 = 7 ∧ acceleratedOrbit 15 23594 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23594) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23594.1, data_15_23594.2]

/-- Complete interval computation for depth 15, residue 23595. -/
theorem bounds_15_23595 : exactInterval 15 23595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23595 : oddCount 23595 15 = 5 ∧ acceleratedOrbit 15 23595 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23595) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23595.1, data_15_23595.2]

/-- Complete interval computation for depth 15, residue 23596. -/
theorem bounds_15_23596 : exactInterval 15 23596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23596 : oddCount 23596 15 = 7 ∧ acceleratedOrbit 15 23596 = 1576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23596) = 3 ^ 7 * m + 1576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23596.1, data_15_23596.2]

/-- Complete interval computation for depth 15, residue 23597. -/
theorem bounds_15_23597 : exactInterval 15 23597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23597 : oddCount 23597 15 = 7 ∧ acceleratedOrbit 15 23597 = 1576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23597) = 3 ^ 7 * m + 1576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23597.1, data_15_23597.2]

/-- Complete interval computation for depth 15, residue 23598. -/
theorem bounds_15_23598 : exactInterval 15 23598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23598 : oddCount 23598 15 = 7 ∧ acceleratedOrbit 15 23598 = 1576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23598) = 3 ^ 7 * m + 1576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23598.1, data_15_23598.2]

/-- Complete interval computation for depth 15, residue 23599. -/
theorem bounds_15_23599 : exactInterval 15 23599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23599 : oddCount 23599 15 = 9 ∧ acceleratedOrbit 15 23599 = 14177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23599) = 3 ^ 9 * m + 14177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23599.1, data_15_23599.2]

/-- Complete interval computation for depth 15, residue 23600. -/
theorem bounds_15_23600 : exactInterval 15 23600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23600 : oddCount 23600 15 = 7 ∧ acceleratedOrbit 15 23600 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23600) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23600.1, data_15_23600.2]

/-- Complete interval computation for depth 15, residue 23601. -/
theorem bounds_15_23601 : exactInterval 15 23601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23601 : oddCount 23601 15 = 7 ∧ acceleratedOrbit 15 23601 = 1576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23601) = 3 ^ 7 * m + 1576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23601.1, data_15_23601.2]

/-- Complete interval computation for depth 15, residue 23602. -/
theorem bounds_15_23602 : exactInterval 15 23602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23602 : oddCount 23602 15 = 7 ∧ acceleratedOrbit 15 23602 = 1576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23602) = 3 ^ 7 * m + 1576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23602.1, data_15_23602.2]

/-- Complete interval computation for depth 15, residue 23603. -/
theorem bounds_15_23603 : exactInterval 15 23603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23603 : oddCount 23603 15 = 7 ∧ acceleratedOrbit 15 23603 = 1576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23603) = 3 ^ 7 * m + 1576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23603.1, data_15_23603.2]

/-- Complete interval computation for depth 15, residue 23604. -/
theorem bounds_15_23604 : exactInterval 15 23604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23604 : oddCount 23604 15 = 7 ∧ acceleratedOrbit 15 23604 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23604) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23604.1, data_15_23604.2]

/-- Complete interval computation for depth 15, residue 23605. -/
theorem bounds_15_23605 : exactInterval 15 23605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23605 : oddCount 23605 15 = 7 ∧ acceleratedOrbit 15 23605 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23605) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23605.1, data_15_23605.2]

/-- Complete interval computation for depth 15, residue 23606. -/
theorem bounds_15_23606 : exactInterval 15 23606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23606 : oddCount 23606 15 = 10 ∧ acceleratedOrbit 15 23606 = 42545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23606) = 3 ^ 10 * m + 42545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23606.1, data_15_23606.2]

/-- Complete interval computation for depth 15, residue 23607. -/
theorem bounds_15_23607 : exactInterval 15 23607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23607 : oddCount 23607 15 = 10 ∧ acceleratedOrbit 15 23607 = 42545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23607) = 3 ^ 10 * m + 42545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23607.1, data_15_23607.2]

/-- Complete interval computation for depth 15, residue 23608. -/
theorem bounds_15_23608 : exactInterval 15 23608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23608 : oddCount 23608 15 = 6 ∧ acceleratedOrbit 15 23608 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23608) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23608.1, data_15_23608.2]

/-- Complete interval computation for depth 15, residue 23609. -/
theorem bounds_15_23609 : exactInterval 15 23609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23609 : oddCount 23609 15 = 7 ∧ acceleratedOrbit 15 23609 = 1576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23609) = 3 ^ 7 * m + 1576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23609.1, data_15_23609.2]

/-- Complete interval computation for depth 15, residue 23610. -/
theorem bounds_15_23610 : exactInterval 15 23610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23610 : oddCount 23610 15 = 6 ∧ acceleratedOrbit 15 23610 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23610) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23610.1, data_15_23610.2]

/-- Complete interval computation for depth 15, residue 23611. -/
theorem bounds_15_23611 : exactInterval 15 23611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23611 : oddCount 23611 15 = 9 ∧ acceleratedOrbit 15 23611 = 14185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23611) = 3 ^ 9 * m + 14185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23611.1, data_15_23611.2]

/-- Complete interval computation for depth 15, residue 23612. -/
theorem bounds_15_23612 : exactInterval 15 23612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23612 : oddCount 23612 15 = 6 ∧ acceleratedOrbit 15 23612 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23612) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23612.1, data_15_23612.2]

/-- Complete interval computation for depth 15, residue 23613. -/
theorem bounds_15_23613 : exactInterval 15 23613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23613 : oddCount 23613 15 = 6 ∧ acceleratedOrbit 15 23613 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23613) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23613.1, data_15_23613.2]

/-- Complete interval computation for depth 15, residue 23614. -/
theorem bounds_15_23614 : exactInterval 15 23614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23614 : oddCount 23614 15 = 9 ∧ acceleratedOrbit 15 23614 = 14186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23614) = 3 ^ 9 * m + 14186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23614.1, data_15_23614.2]

/-- Complete interval computation for depth 15, residue 23615. -/
theorem bounds_15_23615 : exactInterval 15 23615 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23615) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23615 : oddCount 23615 15 = 9 ∧ acceleratedOrbit 15 23615 = 14186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23615) = 3 ^ 9 * m + 14186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23615.1, data_15_23615.2]

/-- Complete interval computation for depth 15, residue 23616. -/
theorem bounds_15_23616 : exactInterval 15 23616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23616 : oddCount 23616 15 = 3 ∧ acceleratedOrbit 15 23616 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23616) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23616.1, data_15_23616.2]

/-- Complete interval computation for depth 15, residue 23617. -/
theorem bounds_15_23617 : exactInterval 15 23617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23617 : oddCount 23617 15 = 7 ∧ acceleratedOrbit 15 23617 = 1577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23617) = 3 ^ 7 * m + 1577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23617.1, data_15_23617.2]

/-- Complete interval computation for depth 15, residue 23618. -/
theorem bounds_15_23618 : exactInterval 15 23618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23618 : oddCount 23618 15 = 7 ∧ acceleratedOrbit 15 23618 = 1577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23618) = 3 ^ 7 * m + 1577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23618.1, data_15_23618.2]

/-- Complete interval computation for depth 15, residue 23619. -/
theorem bounds_15_23619 : exactInterval 15 23619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23619 : oddCount 23619 15 = 7 ∧ acceleratedOrbit 15 23619 = 1577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23619) = 3 ^ 7 * m + 1577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23619.1, data_15_23619.2]

/-- Complete interval computation for depth 15, residue 23620. -/
theorem bounds_15_23620 : exactInterval 15 23620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23620 : oddCount 23620 15 = 7 ∧ acceleratedOrbit 15 23620 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23620) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23620.1, data_15_23620.2]

/-- Complete interval computation for depth 15, residue 23621. -/
theorem bounds_15_23621 : exactInterval 15 23621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23621 : oddCount 23621 15 = 7 ∧ acceleratedOrbit 15 23621 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23621) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23621.1, data_15_23621.2]

/-- Complete interval computation for depth 15, residue 23622. -/
theorem bounds_15_23622 : exactInterval 15 23622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23622 : oddCount 23622 15 = 7 ∧ acceleratedOrbit 15 23622 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23622) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23622.1, data_15_23622.2]

/-- Complete interval computation for depth 15, residue 23623. -/
theorem bounds_15_23623 : exactInterval 15 23623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23623 : oddCount 23623 15 = 9 ∧ acceleratedOrbit 15 23623 = 14192 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23623) = 3 ^ 9 * m + 14192 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23623.1, data_15_23623.2]

/-- Complete interval computation for depth 15, residue 23624. -/
theorem bounds_15_23624 : exactInterval 15 23624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23624 : oddCount 23624 15 = 9 ∧ acceleratedOrbit 15 23624 = 14201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23624) = 3 ^ 9 * m + 14201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23624.1, data_15_23624.2]

end Collatz.Research.PassageAtlas.Batch0721
