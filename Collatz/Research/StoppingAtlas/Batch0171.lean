import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0171

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1587. -/
theorem bounds_11_1587 : exactInterval 11 1587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1587 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1587) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1587 : oddCount 1587 11 = 7 ∧ acceleratedOrbit 11 1587 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1587 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1587) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1587.1, data_11_1587.2]

/-- Complete interval computation for depth 11, residue 1588. -/
theorem bounds_11_1588 : exactInterval 11 1588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1588 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1588) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1588 : oddCount 1588 11 = 2 ∧ acceleratedOrbit 11 1588 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1588 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1588) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1588.1, data_11_1588.2]

/-- Complete interval computation for depth 11, residue 1589. -/
theorem bounds_11_1589 : exactInterval 11 1589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1589 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1589) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1589 : oddCount 1589 11 = 2 ∧ acceleratedOrbit 11 1589 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1589 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1589) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1589.1, data_11_1589.2]

/-- Complete interval computation for depth 11, residue 1590. -/
theorem bounds_11_1590 : exactInterval 11 1590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1590 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1590) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1590 : oddCount 1590 11 = 9 ∧ acceleratedOrbit 11 1590 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1590 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1590) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1590.1, data_11_1590.2]

/-- Complete interval computation for depth 11, residue 1591. -/
theorem bounds_11_1591 : exactInterval 11 1591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1591 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1591) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1591 : oddCount 1591 11 = 9 ∧ acceleratedOrbit 11 1591 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1591 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1591) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1591.1, data_11_1591.2]

/-- Complete interval computation for depth 11, residue 1592. -/
theorem bounds_11_1592 : exactInterval 11 1592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1592 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1592) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1592 : oddCount 1592 11 = 5 ∧ acceleratedOrbit 11 1592 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1592 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1592) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1592.1, data_11_1592.2]

/-- Complete interval computation for depth 11, residue 1593. -/
theorem bounds_11_1593 : exactInterval 11 1593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1593 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1593) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1593 : oddCount 1593 11 = 6 ∧ acceleratedOrbit 11 1593 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1593 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1593) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1593.1, data_11_1593.2]

/-- Complete interval computation for depth 11, residue 1594. -/
theorem bounds_11_1594 : exactInterval 11 1594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1594 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1594) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1594 : oddCount 1594 11 = 5 ∧ acceleratedOrbit 11 1594 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1594 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1594) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1594.1, data_11_1594.2]

/-- Complete interval computation for depth 11, residue 1595. -/
theorem bounds_11_1595 : exactInterval 11 1595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1595 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1595) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1595 : oddCount 1595 11 = 6 ∧ acceleratedOrbit 11 1595 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1595 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1595) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1595.1, data_11_1595.2]

/-- Complete interval computation for depth 11, residue 1596. -/
theorem bounds_11_1596 : exactInterval 11 1596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1596 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1596) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1596 : oddCount 1596 11 = 5 ∧ acceleratedOrbit 11 1596 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1596 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1596) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1596.1, data_11_1596.2]

/-- Complete interval computation for depth 11, residue 1597. -/
theorem bounds_11_1597 : exactInterval 11 1597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1597 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1597) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1597 : oddCount 1597 11 = 5 ∧ acceleratedOrbit 11 1597 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1597 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1597) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1597.1, data_11_1597.2]

/-- Complete interval computation for depth 11, residue 1598. -/
theorem bounds_11_1598 : exactInterval 11 1598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1598 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1598) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1598 : oddCount 1598 11 = 7 ∧ acceleratedOrbit 11 1598 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1598 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1598) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1598.1, data_11_1598.2]

/-- Complete interval computation for depth 11, residue 1599. -/
theorem bounds_11_1599 : exactInterval 11 1599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1599 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1599) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1599 : oddCount 1599 11 = 7 ∧ acceleratedOrbit 11 1599 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1599 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1599) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1599.1, data_11_1599.2]

/-- Complete interval computation for depth 11, residue 1600. -/
theorem bounds_11_1600 : exactInterval 11 1600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1600 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1600) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1600 : oddCount 1600 11 = 3 ∧ acceleratedOrbit 11 1600 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1600 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1600) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1600.1, data_11_1600.2]

/-- Complete interval computation for depth 11, residue 1601. -/
theorem bounds_11_1601 : exactInterval 11 1601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1601 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1601) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1601 : oddCount 1601 11 = 5 ∧ acceleratedOrbit 11 1601 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1601 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1601) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1601.1, data_11_1601.2]

end Collatz.Research.StoppingAtlas.Batch0171
