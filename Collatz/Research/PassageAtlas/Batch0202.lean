import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0202

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6586. -/
theorem bounds_15_6586 : exactInterval 15 6586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6586 : oddCount 6586 15 = 8 ∧ acceleratedOrbit 15 6586 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6586) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6586.1, data_15_6586.2]

/-- Complete interval computation for depth 15, residue 6587. -/
theorem bounds_15_6587 : exactInterval 15 6587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6587 : oddCount 6587 15 = 9 ∧ acceleratedOrbit 15 6587 = 3959 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6587) = 3 ^ 9 * m + 3959 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6587.1, data_15_6587.2]

/-- Complete interval computation for depth 15, residue 6588. -/
theorem bounds_15_6588 : exactInterval 15 6588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6588 : oddCount 6588 15 = 7 ∧ acceleratedOrbit 15 6588 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6588) = 3 ^ 7 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6588.1, data_15_6588.2]

/-- Complete interval computation for depth 15, residue 6589. -/
theorem bounds_15_6589 : exactInterval 15 6589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6589 : oddCount 6589 15 = 7 ∧ acceleratedOrbit 15 6589 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6589) = 3 ^ 7 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6589.1, data_15_6589.2]

/-- Complete interval computation for depth 15, residue 6590. -/
theorem bounds_15_6590 : exactInterval 15 6590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6590 : oddCount 6590 15 = 7 ∧ acceleratedOrbit 15 6590 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6590) = 3 ^ 7 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6590.1, data_15_6590.2]

/-- Complete interval computation for depth 15, residue 6591. -/
theorem bounds_15_6591 : exactInterval 15 6591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6591 : oddCount 6591 15 = 12 ∧ acceleratedOrbit 15 6591 = 106913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6591) = 3 ^ 12 * m + 106913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6591.1, data_15_6591.2]

/-- Complete interval computation for depth 15, residue 6592. -/
theorem bounds_15_6592 : exactInterval 15 6592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6592 : oddCount 6592 15 = 7 ∧ acceleratedOrbit 15 6592 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6592) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6592.1, data_15_6592.2]

/-- Complete interval computation for depth 15, residue 6593. -/
theorem bounds_15_6593 : exactInterval 15 6593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6593 : oddCount 6593 15 = 9 ∧ acceleratedOrbit 15 6593 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6593) = 3 ^ 9 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6593.1, data_15_6593.2]

/-- Complete interval computation for depth 15, residue 6594. -/
theorem bounds_15_6594 : exactInterval 15 6594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6594 : oddCount 6594 15 = 9 ∧ acceleratedOrbit 15 6594 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6594) = 3 ^ 9 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6594.1, data_15_6594.2]

/-- Complete interval computation for depth 15, residue 6595. -/
theorem bounds_15_6595 : exactInterval 15 6595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6595 : oddCount 6595 15 = 9 ∧ acceleratedOrbit 15 6595 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6595) = 3 ^ 9 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6595.1, data_15_6595.2]

/-- Complete interval computation for depth 15, residue 6596. -/
theorem bounds_15_6596 : exactInterval 15 6596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6596 : oddCount 6596 15 = 4 ∧ acceleratedOrbit 15 6596 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6596) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6596.1, data_15_6596.2]

/-- Complete interval computation for depth 15, residue 6597. -/
theorem bounds_15_6597 : exactInterval 15 6597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6597 : oddCount 6597 15 = 4 ∧ acceleratedOrbit 15 6597 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6597) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6597.1, data_15_6597.2]

/-- Complete interval computation for depth 15, residue 6598. -/
theorem bounds_15_6598 : exactInterval 15 6598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6598 : oddCount 6598 15 = 4 ∧ acceleratedOrbit 15 6598 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6598) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6598.1, data_15_6598.2]

/-- Complete interval computation for depth 15, residue 6599. -/
theorem bounds_15_6599 : exactInterval 15 6599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6599 : oddCount 6599 15 = 10 ∧ acceleratedOrbit 15 6599 = 11897 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6599) = 3 ^ 10 * m + 11897 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6599.1, data_15_6599.2]

/-- Complete interval computation for depth 15, residue 6600. -/
theorem bounds_15_6600 : exactInterval 15 6600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6600 : oddCount 6600 15 = 7 ∧ acceleratedOrbit 15 6600 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6600) = 3 ^ 7 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6600.1, data_15_6600.2]

/-- Complete interval computation for depth 15, residue 6601. -/
theorem bounds_15_6601 : exactInterval 15 6601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6601 : oddCount 6601 15 = 10 ∧ acceleratedOrbit 15 6601 = 11906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6601) = 3 ^ 10 * m + 11906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6601.1, data_15_6601.2]

/-- Complete interval computation for depth 15, residue 6602. -/
theorem bounds_15_6602 : exactInterval 15 6602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6602 : oddCount 6602 15 = 7 ∧ acceleratedOrbit 15 6602 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6602) = 3 ^ 7 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6602.1, data_15_6602.2]

/-- Complete interval computation for depth 15, residue 6603. -/
theorem bounds_15_6603 : exactInterval 15 6603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6603 : oddCount 6603 15 = 5 ∧ acceleratedOrbit 15 6603 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6603) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6603.1, data_15_6603.2]

/-- Complete interval computation for depth 15, residue 6604. -/
theorem bounds_15_6604 : exactInterval 15 6604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6604 : oddCount 6604 15 = 7 ∧ acceleratedOrbit 15 6604 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6604) = 3 ^ 7 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6604.1, data_15_6604.2]

/-- Complete interval computation for depth 15, residue 6605. -/
theorem bounds_15_6605 : exactInterval 15 6605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6605 : oddCount 6605 15 = 7 ∧ acceleratedOrbit 15 6605 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6605) = 3 ^ 7 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6605.1, data_15_6605.2]

/-- Complete interval computation for depth 15, residue 6606. -/
theorem bounds_15_6606 : exactInterval 15 6606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6606 : oddCount 6606 15 = 9 ∧ acceleratedOrbit 15 6606 = 3970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6606) = 3 ^ 9 * m + 3970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6606.1, data_15_6606.2]

/-- Complete interval computation for depth 15, residue 6607. -/
theorem bounds_15_6607 : exactInterval 15 6607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6607 : oddCount 6607 15 = 9 ∧ acceleratedOrbit 15 6607 = 3970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6607) = 3 ^ 9 * m + 3970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6607.1, data_15_6607.2]

/-- Complete interval computation for depth 15, residue 6608. -/
theorem bounds_15_6608 : exactInterval 15 6608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6608 : oddCount 6608 15 = 7 ∧ acceleratedOrbit 15 6608 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6608) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6608.1, data_15_6608.2]

/-- Complete interval computation for depth 15, residue 6609. -/
theorem bounds_15_6609 : exactInterval 15 6609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6609 : oddCount 6609 15 = 7 ∧ acceleratedOrbit 15 6609 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6609) = 3 ^ 7 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6609.1, data_15_6609.2]

/-- Complete interval computation for depth 15, residue 6610. -/
theorem bounds_15_6610 : exactInterval 15 6610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6610 : oddCount 6610 15 = 8 ∧ acceleratedOrbit 15 6610 = 1325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6610) = 3 ^ 8 * m + 1325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6610.1, data_15_6610.2]

/-- Complete interval computation for depth 15, residue 6611. -/
theorem bounds_15_6611 : exactInterval 15 6611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6611 : oddCount 6611 15 = 8 ∧ acceleratedOrbit 15 6611 = 1325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6611) = 3 ^ 8 * m + 1325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6611.1, data_15_6611.2]

/-- Complete interval computation for depth 15, residue 6612. -/
theorem bounds_15_6612 : exactInterval 15 6612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6612 : oddCount 6612 15 = 7 ∧ acceleratedOrbit 15 6612 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6612) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6612.1, data_15_6612.2]

/-- Complete interval computation for depth 15, residue 6613. -/
theorem bounds_15_6613 : exactInterval 15 6613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6613 : oddCount 6613 15 = 7 ∧ acceleratedOrbit 15 6613 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6613) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6613.1, data_15_6613.2]

/-- Complete interval computation for depth 15, residue 6614. -/
theorem bounds_15_6614 : exactInterval 15 6614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6614 : oddCount 6614 15 = 10 ∧ acceleratedOrbit 15 6614 = 11927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6614) = 3 ^ 10 * m + 11927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6614.1, data_15_6614.2]

/-- Complete interval computation for depth 15, residue 6615. -/
theorem bounds_15_6615 : exactInterval 15 6615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6615 : oddCount 6615 15 = 10 ∧ acceleratedOrbit 15 6615 = 11927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6615) = 3 ^ 10 * m + 11927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6615.1, data_15_6615.2]

/-- Complete interval computation for depth 15, residue 6616. -/
theorem bounds_15_6616 : exactInterval 15 6616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6616 : oddCount 6616 15 = 6 ∧ acceleratedOrbit 15 6616 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6616) = 3 ^ 6 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6616.1, data_15_6616.2]

/-- Complete interval computation for depth 15, residue 6617. -/
theorem bounds_15_6617 : exactInterval 15 6617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6617 : oddCount 6617 15 = 6 ∧ acceleratedOrbit 15 6617 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6617) = 3 ^ 6 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6617.1, data_15_6617.2]

/-- Complete interval computation for depth 15, residue 6618. -/
theorem bounds_15_6618 : exactInterval 15 6618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6618 : oddCount 6618 15 = 6 ∧ acceleratedOrbit 15 6618 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6618) = 3 ^ 6 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6618.1, data_15_6618.2]

end Collatz.Research.PassageAtlas.Batch0202
