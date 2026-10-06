import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0965

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31588. -/
theorem bounds_15_31588 : exactInterval 15 31588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31588 : oddCount 31588 15 = 6 ∧ acceleratedOrbit 15 31588 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31588) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31588.1, data_15_31588.2]

/-- Complete interval computation for depth 15, residue 31589. -/
theorem bounds_15_31589 : exactInterval 15 31589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31589 : oddCount 31589 15 = 6 ∧ acceleratedOrbit 15 31589 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31589) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31589.1, data_15_31589.2]

/-- Complete interval computation for depth 15, residue 31590. -/
theorem bounds_15_31590 : exactInterval 15 31590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31590 : oddCount 31590 15 = 6 ∧ acceleratedOrbit 15 31590 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31590) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31590.1, data_15_31590.2]

/-- Complete interval computation for depth 15, residue 31591. -/
theorem bounds_15_31591 : exactInterval 15 31591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31591 : oddCount 31591 15 = 11 ∧ acceleratedOrbit 15 31591 = 170792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31591) = 3 ^ 11 * m + 170792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31591.1, data_15_31591.2]

/-- Complete interval computation for depth 15, residue 31592. -/
theorem bounds_15_31592 : exactInterval 15 31592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31592 : oddCount 31592 15 = 6 ∧ acceleratedOrbit 15 31592 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31592) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31592.1, data_15_31592.2]

/-- Complete interval computation for depth 15, residue 31593. -/
theorem bounds_15_31593 : exactInterval 15 31593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31593 : oddCount 31593 15 = 9 ∧ acceleratedOrbit 15 31593 = 18980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31593) = 3 ^ 9 * m + 18980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31593.1, data_15_31593.2]

/-- Complete interval computation for depth 15, residue 31594. -/
theorem bounds_15_31594 : exactInterval 15 31594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31594 : oddCount 31594 15 = 6 ∧ acceleratedOrbit 15 31594 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31594) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31594.1, data_15_31594.2]

/-- Complete interval computation for depth 15, residue 31595. -/
theorem bounds_15_31595 : exactInterval 15 31595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31595 : oddCount 31595 15 = 6 ∧ acceleratedOrbit 15 31595 = 703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31595) = 3 ^ 6 * m + 703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31595.1, data_15_31595.2]

/-- Complete interval computation for depth 15, residue 31596. -/
theorem bounds_15_31596 : exactInterval 15 31596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31596 : oddCount 31596 15 = 8 ∧ acceleratedOrbit 15 31596 = 6328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31596) = 3 ^ 8 * m + 6328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31596.1, data_15_31596.2]

/-- Complete interval computation for depth 15, residue 31597. -/
theorem bounds_15_31597 : exactInterval 15 31597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31597 : oddCount 31597 15 = 8 ∧ acceleratedOrbit 15 31597 = 6328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31597) = 3 ^ 8 * m + 6328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31597.1, data_15_31597.2]

/-- Complete interval computation for depth 15, residue 31598. -/
theorem bounds_15_31598 : exactInterval 15 31598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31598 : oddCount 31598 15 = 8 ∧ acceleratedOrbit 15 31598 = 6328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31598) = 3 ^ 8 * m + 6328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31598.1, data_15_31598.2]

/-- Complete interval computation for depth 15, residue 31599. -/
theorem bounds_15_31599 : exactInterval 15 31599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31599 : oddCount 31599 15 = 9 ∧ acceleratedOrbit 15 31599 = 18982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31599) = 3 ^ 9 * m + 18982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31599.1, data_15_31599.2]

/-- Complete interval computation for depth 15, residue 31600. -/
theorem bounds_15_31600 : exactInterval 15 31600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31600 : oddCount 31600 15 = 6 ∧ acceleratedOrbit 15 31600 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31600) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31600.1, data_15_31600.2]

/-- Complete interval computation for depth 15, residue 31601. -/
theorem bounds_15_31601 : exactInterval 15 31601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31601 : oddCount 31601 15 = 6 ∧ acceleratedOrbit 15 31601 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31601) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31601.1, data_15_31601.2]

/-- Complete interval computation for depth 15, residue 31602. -/
theorem bounds_15_31602 : exactInterval 15 31602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31602 : oddCount 31602 15 = 6 ∧ acceleratedOrbit 15 31602 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31602) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31602.1, data_15_31602.2]

/-- Complete interval computation for depth 15, residue 31603. -/
theorem bounds_15_31603 : exactInterval 15 31603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31603 : oddCount 31603 15 = 6 ∧ acceleratedOrbit 15 31603 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31603) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31603.1, data_15_31603.2]

/-- Complete interval computation for depth 15, residue 31604. -/
theorem bounds_15_31604 : exactInterval 15 31604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31604 : oddCount 31604 15 = 6 ∧ acceleratedOrbit 15 31604 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31604) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31604.1, data_15_31604.2]

/-- Complete interval computation for depth 15, residue 31605. -/
theorem bounds_15_31605 : exactInterval 15 31605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31605 : oddCount 31605 15 = 6 ∧ acceleratedOrbit 15 31605 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31605) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31605.1, data_15_31605.2]

/-- Complete interval computation for depth 15, residue 31606. -/
theorem bounds_15_31606 : exactInterval 15 31606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31606 : oddCount 31606 15 = 7 ∧ acceleratedOrbit 15 31606 = 2110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31606) = 3 ^ 7 * m + 2110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31606.1, data_15_31606.2]

/-- Complete interval computation for depth 15, residue 31607. -/
theorem bounds_15_31607 : exactInterval 15 31607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31607 : oddCount 31607 15 = 7 ∧ acceleratedOrbit 15 31607 = 2110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31607) = 3 ^ 7 * m + 2110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31607.1, data_15_31607.2]

/-- Complete interval computation for depth 15, residue 31608. -/
theorem bounds_15_31608 : exactInterval 15 31608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31608 : oddCount 31608 15 = 8 ∧ acceleratedOrbit 15 31608 = 6331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31608) = 3 ^ 8 * m + 6331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31608.1, data_15_31608.2]

/-- Complete interval computation for depth 15, residue 31609. -/
theorem bounds_15_31609 : exactInterval 15 31609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31609 : oddCount 31609 15 = 10 ∧ acceleratedOrbit 15 31609 = 56965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31609) = 3 ^ 10 * m + 56965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31609.1, data_15_31609.2]

/-- Complete interval computation for depth 15, residue 31610. -/
theorem bounds_15_31610 : exactInterval 15 31610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31610 : oddCount 31610 15 = 8 ∧ acceleratedOrbit 15 31610 = 6331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31610) = 3 ^ 8 * m + 6331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31610.1, data_15_31610.2]

/-- Complete interval computation for depth 15, residue 31611. -/
theorem bounds_15_31611 : exactInterval 15 31611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31611 : oddCount 31611 15 = 10 ∧ acceleratedOrbit 15 31611 = 56969 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31611) = 3 ^ 10 * m + 56969 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31611.1, data_15_31611.2]

/-- Complete interval computation for depth 15, residue 31612. -/
theorem bounds_15_31612 : exactInterval 15 31612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31612 : oddCount 31612 15 = 8 ∧ acceleratedOrbit 15 31612 = 6331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31612) = 3 ^ 8 * m + 6331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31612.1, data_15_31612.2]

/-- Complete interval computation for depth 15, residue 31613. -/
theorem bounds_15_31613 : exactInterval 15 31613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31613 : oddCount 31613 15 = 8 ∧ acceleratedOrbit 15 31613 = 6331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31613) = 3 ^ 8 * m + 6331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31613.1, data_15_31613.2]

/-- Complete interval computation for depth 15, residue 31614. -/
theorem bounds_15_31614 : exactInterval 15 31614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31614 : oddCount 31614 15 = 11 ∧ acceleratedOrbit 15 31614 = 170920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31614) = 3 ^ 11 * m + 170920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31614.1, data_15_31614.2]

/-- Complete interval computation for depth 15, residue 31615. -/
theorem bounds_15_31615 : exactInterval 15 31615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31615 : oddCount 31615 15 = 11 ∧ acceleratedOrbit 15 31615 = 170920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31615) = 3 ^ 11 * m + 170920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31615.1, data_15_31615.2]

/-- Complete interval computation for depth 15, residue 31616. -/
theorem bounds_15_31616 : exactInterval 15 31616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31616 : oddCount 31616 15 = 5 ∧ acceleratedOrbit 15 31616 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31616) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31616.1, data_15_31616.2]

/-- Complete interval computation for depth 15, residue 31617. -/
theorem bounds_15_31617 : exactInterval 15 31617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31617 : oddCount 31617 15 = 10 ∧ acceleratedOrbit 15 31617 = 56983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31617) = 3 ^ 10 * m + 56983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31617.1, data_15_31617.2]

/-- Complete interval computation for depth 15, residue 31618. -/
theorem bounds_15_31618 : exactInterval 15 31618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31618 : oddCount 31618 15 = 7 ∧ acceleratedOrbit 15 31618 = 2111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31618) = 3 ^ 7 * m + 2111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31618.1, data_15_31618.2]

/-- Complete interval computation for depth 15, residue 31619. -/
theorem bounds_15_31619 : exactInterval 15 31619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31619 : oddCount 31619 15 = 7 ∧ acceleratedOrbit 15 31619 = 2111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31619) = 3 ^ 7 * m + 2111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31619.1, data_15_31619.2]

/-- Complete interval computation for depth 15, residue 31620. -/
theorem bounds_15_31620 : exactInterval 15 31620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31620 : oddCount 31620 15 = 7 ∧ acceleratedOrbit 15 31620 = 2111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31620) = 3 ^ 7 * m + 2111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31620.1, data_15_31620.2]

end Collatz.Research.PassageAtlas.Batch0965
