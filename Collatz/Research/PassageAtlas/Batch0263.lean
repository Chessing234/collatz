import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0263

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8585. -/
theorem bounds_15_8585 : exactInterval 15 8585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8585 : oddCount 8585 15 = 9 ∧ acceleratedOrbit 15 8585 = 5159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8585) = 3 ^ 9 * m + 5159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8585.1, data_15_8585.2]

/-- Complete interval computation for depth 15, residue 8586. -/
theorem bounds_15_8586 : exactInterval 15 8586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8586 : oddCount 8586 15 = 5 ∧ acceleratedOrbit 15 8586 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8586) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8586.1, data_15_8586.2]

/-- Complete interval computation for depth 15, residue 8587. -/
theorem bounds_15_8587 : exactInterval 15 8587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8587 : oddCount 8587 15 = 8 ∧ acceleratedOrbit 15 8587 = 1720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8587) = 3 ^ 8 * m + 1720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8587.1, data_15_8587.2]

/-- Complete interval computation for depth 15, residue 8588. -/
theorem bounds_15_8588 : exactInterval 15 8588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8588 : oddCount 8588 15 = 5 ∧ acceleratedOrbit 15 8588 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8588) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8588.1, data_15_8588.2]

/-- Complete interval computation for depth 15, residue 8589. -/
theorem bounds_15_8589 : exactInterval 15 8589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8589 : oddCount 8589 15 = 5 ∧ acceleratedOrbit 15 8589 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8589) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8589.1, data_15_8589.2]

/-- Complete interval computation for depth 15, residue 8590. -/
theorem bounds_15_8590 : exactInterval 15 8590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8590 : oddCount 8590 15 = 8 ∧ acceleratedOrbit 15 8590 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8590) = 3 ^ 8 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8590.1, data_15_8590.2]

/-- Complete interval computation for depth 15, residue 8591. -/
theorem bounds_15_8591 : exactInterval 15 8591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8591 : oddCount 8591 15 = 8 ∧ acceleratedOrbit 15 8591 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8591) = 3 ^ 8 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8591.1, data_15_8591.2]

/-- Complete interval computation for depth 15, residue 8592. -/
theorem bounds_15_8592 : exactInterval 15 8592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8592 : oddCount 8592 15 = 5 ∧ acceleratedOrbit 15 8592 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8592) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8592.1, data_15_8592.2]

/-- Complete interval computation for depth 15, residue 8593. -/
theorem bounds_15_8593 : exactInterval 15 8593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8593 : oddCount 8593 15 = 5 ∧ acceleratedOrbit 15 8593 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8593) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8593.1, data_15_8593.2]

/-- Complete interval computation for depth 15, residue 8594. -/
theorem bounds_15_8594 : exactInterval 15 8594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8594 : oddCount 8594 15 = 5 ∧ acceleratedOrbit 15 8594 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8594) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8594.1, data_15_8594.2]

/-- Complete interval computation for depth 15, residue 8595. -/
theorem bounds_15_8595 : exactInterval 15 8595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8595 : oddCount 8595 15 = 5 ∧ acceleratedOrbit 15 8595 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8595) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8595.1, data_15_8595.2]

/-- Complete interval computation for depth 15, residue 8596. -/
theorem bounds_15_8596 : exactInterval 15 8596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8596 : oddCount 8596 15 = 5 ∧ acceleratedOrbit 15 8596 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8596) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8596.1, data_15_8596.2]

/-- Complete interval computation for depth 15, residue 8597. -/
theorem bounds_15_8597 : exactInterval 15 8597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8597 : oddCount 8597 15 = 5 ∧ acceleratedOrbit 15 8597 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8597) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8597.1, data_15_8597.2]

/-- Complete interval computation for depth 15, residue 8598. -/
theorem bounds_15_8598 : exactInterval 15 8598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8598 : oddCount 8598 15 = 7 ∧ acceleratedOrbit 15 8598 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8598) = 3 ^ 7 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8598.1, data_15_8598.2]

/-- Complete interval computation for depth 15, residue 8599. -/
theorem bounds_15_8599 : exactInterval 15 8599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8599 : oddCount 8599 15 = 7 ∧ acceleratedOrbit 15 8599 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8599) = 3 ^ 7 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8599.1, data_15_8599.2]

/-- Complete interval computation for depth 15, residue 8600. -/
theorem bounds_15_8600 : exactInterval 15 8600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8600 : oddCount 8600 15 = 5 ∧ acceleratedOrbit 15 8600 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8600) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8600.1, data_15_8600.2]

/-- Complete interval computation for depth 15, residue 8601. -/
theorem bounds_15_8601 : exactInterval 15 8601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8601 : oddCount 8601 15 = 7 ∧ acceleratedOrbit 15 8601 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8601) = 3 ^ 7 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8601.1, data_15_8601.2]

/-- Complete interval computation for depth 15, residue 8602. -/
theorem bounds_15_8602 : exactInterval 15 8602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8602 : oddCount 8602 15 = 5 ∧ acceleratedOrbit 15 8602 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8602) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8602.1, data_15_8602.2]

/-- Complete interval computation for depth 15, residue 8603. -/
theorem bounds_15_8603 : exactInterval 15 8603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8603 : oddCount 8603 15 = 11 ∧ acceleratedOrbit 15 8603 = 46520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8603) = 3 ^ 11 * m + 46520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8603.1, data_15_8603.2]

/-- Complete interval computation for depth 15, residue 8604. -/
theorem bounds_15_8604 : exactInterval 15 8604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8604 : oddCount 8604 15 = 10 ∧ acceleratedOrbit 15 8604 = 15515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8604) = 3 ^ 10 * m + 15515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8604.1, data_15_8604.2]

/-- Complete interval computation for depth 15, residue 8605. -/
theorem bounds_15_8605 : exactInterval 15 8605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8605 : oddCount 8605 15 = 10 ∧ acceleratedOrbit 15 8605 = 15515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8605) = 3 ^ 10 * m + 15515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8605.1, data_15_8605.2]

/-- Complete interval computation for depth 15, residue 8606. -/
theorem bounds_15_8606 : exactInterval 15 8606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8606 : oddCount 8606 15 = 10 ∧ acceleratedOrbit 15 8606 = 15515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8606) = 3 ^ 10 * m + 15515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8606.1, data_15_8606.2]

/-- Complete interval computation for depth 15, residue 8607. -/
theorem bounds_15_8607 : exactInterval 15 8607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8607 : oddCount 8607 15 = 11 ∧ acceleratedOrbit 15 8607 = 46538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8607) = 3 ^ 11 * m + 46538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8607.1, data_15_8607.2]

/-- Complete interval computation for depth 15, residue 8608. -/
theorem bounds_15_8608 : exactInterval 15 8608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8608 : oddCount 8608 15 = 4 ∧ acceleratedOrbit 15 8608 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8608) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8608.1, data_15_8608.2]

/-- Complete interval computation for depth 15, residue 8609. -/
theorem bounds_15_8609 : exactInterval 15 8609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8609 : oddCount 8609 15 = 9 ∧ acceleratedOrbit 15 8609 = 5174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8609) = 3 ^ 9 * m + 5174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8609.1, data_15_8609.2]

/-- Complete interval computation for depth 15, residue 8610. -/
theorem bounds_15_8610 : exactInterval 15 8610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8610 : oddCount 8610 15 = 8 ∧ acceleratedOrbit 15 8610 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8610) = 3 ^ 8 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8610.1, data_15_8610.2]

/-- Complete interval computation for depth 15, residue 8611. -/
theorem bounds_15_8611 : exactInterval 15 8611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8611 : oddCount 8611 15 = 8 ∧ acceleratedOrbit 15 8611 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8611) = 3 ^ 8 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8611.1, data_15_8611.2]

/-- Complete interval computation for depth 15, residue 8612. -/
theorem bounds_15_8612 : exactInterval 15 8612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8612 : oddCount 8612 15 = 8 ∧ acceleratedOrbit 15 8612 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8612) = 3 ^ 8 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8612.1, data_15_8612.2]

/-- Complete interval computation for depth 15, residue 8613. -/
theorem bounds_15_8613 : exactInterval 15 8613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8613 : oddCount 8613 15 = 8 ∧ acceleratedOrbit 15 8613 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8613) = 3 ^ 8 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8613.1, data_15_8613.2]

/-- Complete interval computation for depth 15, residue 8614. -/
theorem bounds_15_8614 : exactInterval 15 8614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8614 : oddCount 8614 15 = 8 ∧ acceleratedOrbit 15 8614 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8614) = 3 ^ 8 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8614.1, data_15_8614.2]

/-- Complete interval computation for depth 15, residue 8615. -/
theorem bounds_15_8615 : exactInterval 15 8615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8615 : oddCount 8615 15 = 9 ∧ acceleratedOrbit 15 8615 = 5177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8615) = 3 ^ 9 * m + 5177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8615.1, data_15_8615.2]

/-- Complete interval computation for depth 15, residue 8616. -/
theorem bounds_15_8616 : exactInterval 15 8616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8616 : oddCount 8616 15 = 4 ∧ acceleratedOrbit 15 8616 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8616) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8616.1, data_15_8616.2]

end Collatz.Research.PassageAtlas.Batch0263
