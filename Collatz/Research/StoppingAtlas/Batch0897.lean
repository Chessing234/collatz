import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0897

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6594. -/
theorem bounds_13_6594 : exactInterval 13 6594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6594 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6594) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6594 : oddCount 6594 13 = 8 ∧ acceleratedOrbit 13 6594 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6594 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6594) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6594.1, data_13_6594.2]

/-- Complete interval computation for depth 13, residue 6595. -/
theorem bounds_13_6595 : exactInterval 13 6595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6595 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6595) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6595 : oddCount 6595 13 = 8 ∧ acceleratedOrbit 13 6595 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6595 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6595) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6595.1, data_13_6595.2]

/-- Complete interval computation for depth 13, residue 6596. -/
theorem bounds_13_6596 : exactInterval 13 6596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6596 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6596) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6596 : oddCount 6596 13 = 3 ∧ acceleratedOrbit 13 6596 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6596 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6596) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6596.1, data_13_6596.2]

/-- Complete interval computation for depth 13, residue 6597. -/
theorem bounds_13_6597 : exactInterval 13 6597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6597 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6597) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6597 : oddCount 6597 13 = 3 ∧ acceleratedOrbit 13 6597 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6597 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6597) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6597.1, data_13_6597.2]

/-- Complete interval computation for depth 13, residue 6598. -/
theorem bounds_13_6598 : exactInterval 13 6598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6598 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6598) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6598 : oddCount 6598 13 = 3 ∧ acceleratedOrbit 13 6598 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6598 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6598) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6598.1, data_13_6598.2]

/-- Complete interval computation for depth 13, residue 6599. -/
theorem bounds_13_6599 : exactInterval 13 6599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6599 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6599) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6599 : oddCount 6599 13 = 8 ∧ acceleratedOrbit 13 6599 = 5287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6599 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6599) = 3 ^ 8 * m + 5287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6599.1, data_13_6599.2]

/-- Complete interval computation for depth 13, residue 6600. -/
theorem bounds_13_6600 : exactInterval 13 6600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6600 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6600) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6600 : oddCount 6600 13 = 6 ∧ acceleratedOrbit 13 6600 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6600 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6600) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6600.1, data_13_6600.2]

/-- Complete interval computation for depth 13, residue 6601. -/
theorem bounds_13_6601 : exactInterval 13 6601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6601 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6601) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6601 : oddCount 6601 13 = 8 ∧ acceleratedOrbit 13 6601 = 5291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6601 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6601) = 3 ^ 8 * m + 5291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6601.1, data_13_6601.2]

/-- Complete interval computation for depth 13, residue 6602. -/
theorem bounds_13_6602 : exactInterval 13 6602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6602 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6602) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6602 : oddCount 6602 13 = 6 ∧ acceleratedOrbit 13 6602 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6602 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6602) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6602.1, data_13_6602.2]

/-- Complete interval computation for depth 13, residue 6603. -/
theorem bounds_13_6603 : exactInterval 13 6603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6603 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6603) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6603 : oddCount 6603 13 = 5 ∧ acceleratedOrbit 13 6603 = 196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6603 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6603) = 3 ^ 5 * m + 196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6603.1, data_13_6603.2]

/-- Complete interval computation for depth 13, residue 6604. -/
theorem bounds_13_6604 : exactInterval 13 6604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6604 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6604) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6604 : oddCount 6604 13 = 6 ∧ acceleratedOrbit 13 6604 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6604 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6604) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6604.1, data_13_6604.2]

/-- Complete interval computation for depth 13, residue 6605. -/
theorem bounds_13_6605 : exactInterval 13 6605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6605 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6605) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6605 : oddCount 6605 13 = 6 ∧ acceleratedOrbit 13 6605 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6605 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6605) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6605.1, data_13_6605.2]

/-- Complete interval computation for depth 13, residue 6606. -/
theorem bounds_13_6606 : exactInterval 13 6606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6606 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6606) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6606 : oddCount 6606 13 = 8 ∧ acceleratedOrbit 13 6606 = 5293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6606 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6606) = 3 ^ 8 * m + 5293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6606.1, data_13_6606.2]

/-- Complete interval computation for depth 13, residue 6607. -/
theorem bounds_13_6607 : exactInterval 13 6607 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6607 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6607) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6607 : oddCount 6607 13 = 8 ∧ acceleratedOrbit 13 6607 = 5293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6607 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6607) = 3 ^ 8 * m + 5293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6607.1, data_13_6607.2]

/-- Complete interval computation for depth 13, residue 6608. -/
theorem bounds_13_6608 : exactInterval 13 6608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6608 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6608) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6608 : oddCount 6608 13 = 6 ∧ acceleratedOrbit 13 6608 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6608 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6608) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6608.1, data_13_6608.2]

end Collatz.Research.StoppingAtlas.Batch0897
