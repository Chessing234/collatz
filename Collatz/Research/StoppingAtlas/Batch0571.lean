import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0571

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1587. -/
theorem bounds_13_1587 : exactInterval 13 1587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1587 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1587) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1587 : oddCount 1587 13 = 7 ∧ acceleratedOrbit 13 1587 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1587 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1587) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1587.1, data_13_1587.2]

/-- Complete interval computation for depth 13, residue 1588. -/
theorem bounds_13_1588 : exactInterval 13 1588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1588 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1588) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1588 : oddCount 1588 13 = 4 ∧ acceleratedOrbit 13 1588 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1588 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1588) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1588.1, data_13_1588.2]

/-- Complete interval computation for depth 13, residue 1589. -/
theorem bounds_13_1589 : exactInterval 13 1589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1589 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1589) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1589 : oddCount 1589 13 = 4 ∧ acceleratedOrbit 13 1589 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1589 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1589) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1589.1, data_13_1589.2]

/-- Complete interval computation for depth 13, residue 1590. -/
theorem bounds_13_1590 : exactInterval 13 1590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1590 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1590) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1590 : oddCount 1590 13 = 9 ∧ acceleratedOrbit 13 1590 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1590 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1590) = 3 ^ 9 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1590.1, data_13_1590.2]

/-- Complete interval computation for depth 13, residue 1591. -/
theorem bounds_13_1591 : exactInterval 13 1591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1591 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1591) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1591 : oddCount 1591 13 = 9 ∧ acceleratedOrbit 13 1591 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1591 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1591) = 3 ^ 9 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1591.1, data_13_1591.2]

/-- Complete interval computation for depth 13, residue 1592. -/
theorem bounds_13_1592 : exactInterval 13 1592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1592 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1592) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1592 : oddCount 1592 13 = 6 ∧ acceleratedOrbit 13 1592 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1592 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1592) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1592.1, data_13_1592.2]

/-- Complete interval computation for depth 13, residue 1593. -/
theorem bounds_13_1593 : exactInterval 13 1593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1593 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1593) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1593 : oddCount 1593 13 = 6 ∧ acceleratedOrbit 13 1593 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1593 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1593) = 3 ^ 6 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1593.1, data_13_1593.2]

/-- Complete interval computation for depth 13, residue 1594. -/
theorem bounds_13_1594 : exactInterval 13 1594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1594 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1594) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1594 : oddCount 1594 13 = 6 ∧ acceleratedOrbit 13 1594 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1594 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1594) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1594.1, data_13_1594.2]

/-- Complete interval computation for depth 13, residue 1595. -/
theorem bounds_13_1595 : exactInterval 13 1595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1595 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1595) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1595 : oddCount 1595 13 = 7 ∧ acceleratedOrbit 13 1595 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1595 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1595) = 3 ^ 7 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1595.1, data_13_1595.2]

/-- Complete interval computation for depth 13, residue 1596. -/
theorem bounds_13_1596 : exactInterval 13 1596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1596 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1596) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1596 : oddCount 1596 13 = 6 ∧ acceleratedOrbit 13 1596 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1596 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1596) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1596.1, data_13_1596.2]

/-- Complete interval computation for depth 13, residue 1597. -/
theorem bounds_13_1597 : exactInterval 13 1597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1597 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1597) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1597 : oddCount 1597 13 = 6 ∧ acceleratedOrbit 13 1597 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1597 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1597) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1597.1, data_13_1597.2]

/-- Complete interval computation for depth 13, residue 1598. -/
theorem bounds_13_1598 : exactInterval 13 1598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1598 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1598) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1598 : oddCount 1598 13 = 8 ∧ acceleratedOrbit 13 1598 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1598 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1598) = 3 ^ 8 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1598.1, data_13_1598.2]

/-- Complete interval computation for depth 13, residue 1599. -/
theorem bounds_13_1599 : exactInterval 13 1599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1599 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1599) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1599 : oddCount 1599 13 = 8 ∧ acceleratedOrbit 13 1599 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1599 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1599) = 3 ^ 8 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1599.1, data_13_1599.2]

/-- Complete interval computation for depth 13, residue 1600. -/
theorem bounds_13_1600 : exactInterval 13 1600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1600 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1600) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1600 : oddCount 1600 13 = 4 ∧ acceleratedOrbit 13 1600 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1600 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1600) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1600.1, data_13_1600.2]

/-- Complete interval computation for depth 13, residue 1601. -/
theorem bounds_13_1601 : exactInterval 13 1601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1601 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1601) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1601 : oddCount 1601 13 = 7 ∧ acceleratedOrbit 13 1601 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1601 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1601) = 3 ^ 7 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1601.1, data_13_1601.2]

end Collatz.Research.StoppingAtlas.Batch0571
