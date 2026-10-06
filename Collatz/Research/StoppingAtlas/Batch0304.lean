import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0304

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1582. -/
theorem bounds_12_1582 : exactInterval 12 1582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1582 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1582) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1582 : oddCount 1582 12 = 6 ∧ acceleratedOrbit 12 1582 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1582 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1582) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1582.1, data_12_1582.2]

/-- Complete interval computation for depth 12, residue 1583. -/
theorem bounds_12_1583 : exactInterval 12 1583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1583 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1583) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1583 : oddCount 1583 12 = 10 ∧ acceleratedOrbit 12 1583 = 22841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1583 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1583) = 3 ^ 10 * m + 22841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1583.1, data_12_1583.2]

/-- Complete interval computation for depth 12, residue 1584. -/
theorem bounds_12_1584 : exactInterval 12 1584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1584 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1584) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1584 : oddCount 1584 12 = 3 ∧ acceleratedOrbit 12 1584 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1584 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1584) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1584.1, data_12_1584.2]

/-- Complete interval computation for depth 12, residue 1585. -/
theorem bounds_12_1585 : exactInterval 12 1585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1585 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1585) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1585 : oddCount 1585 12 = 7 ∧ acceleratedOrbit 12 1585 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1585 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1585) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1585.1, data_12_1585.2]

/-- Complete interval computation for depth 12, residue 1586. -/
theorem bounds_12_1586 : exactInterval 12 1586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1586 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1586) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1586 : oddCount 1586 12 = 7 ∧ acceleratedOrbit 12 1586 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1586 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1586) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1586.1, data_12_1586.2]

/-- Complete interval computation for depth 12, residue 1587. -/
theorem bounds_12_1587 : exactInterval 12 1587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1587 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1587) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1587 : oddCount 1587 12 = 7 ∧ acceleratedOrbit 12 1587 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1587 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1587) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1587.1, data_12_1587.2]

/-- Complete interval computation for depth 12, residue 1588. -/
theorem bounds_12_1588 : exactInterval 12 1588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1588 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1588) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1588 : oddCount 1588 12 = 3 ∧ acceleratedOrbit 12 1588 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1588 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1588) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1588.1, data_12_1588.2]

/-- Complete interval computation for depth 12, residue 1589. -/
theorem bounds_12_1589 : exactInterval 12 1589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1589 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1589) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1589 : oddCount 1589 12 = 3 ∧ acceleratedOrbit 12 1589 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1589 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1589) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1589.1, data_12_1589.2]

/-- Complete interval computation for depth 12, residue 1590. -/
theorem bounds_12_1590 : exactInterval 12 1590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1590 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1590) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1590 : oddCount 1590 12 = 9 ∧ acceleratedOrbit 12 1590 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1590 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1590) = 3 ^ 9 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1590.1, data_12_1590.2]

/-- Complete interval computation for depth 12, residue 1591. -/
theorem bounds_12_1591 : exactInterval 12 1591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1591 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1591) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1591 : oddCount 1591 12 = 9 ∧ acceleratedOrbit 12 1591 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1591 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1591) = 3 ^ 9 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1591.1, data_12_1591.2]

/-- Complete interval computation for depth 12, residue 1592. -/
theorem bounds_12_1592 : exactInterval 12 1592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1592 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1592) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1592 : oddCount 1592 12 = 5 ∧ acceleratedOrbit 12 1592 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1592 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1592) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1592.1, data_12_1592.2]

/-- Complete interval computation for depth 12, residue 1593. -/
theorem bounds_12_1593 : exactInterval 12 1593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1593 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1593) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1593 : oddCount 1593 12 = 6 ∧ acceleratedOrbit 12 1593 = 284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1593 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1593) = 3 ^ 6 * m + 284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1593.1, data_12_1593.2]

/-- Complete interval computation for depth 12, residue 1594. -/
theorem bounds_12_1594 : exactInterval 12 1594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1594 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1594) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1594 : oddCount 1594 12 = 5 ∧ acceleratedOrbit 12 1594 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1594 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1594) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1594.1, data_12_1594.2]

/-- Complete interval computation for depth 12, residue 1595. -/
theorem bounds_12_1595 : exactInterval 12 1595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1595 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1595) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1595 : oddCount 1595 12 = 7 ∧ acceleratedOrbit 12 1595 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1595 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1595) = 3 ^ 7 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1595.1, data_12_1595.2]

/-- Complete interval computation for depth 12, residue 1596. -/
theorem bounds_12_1596 : exactInterval 12 1596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1596 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1596) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1596 : oddCount 1596 12 = 5 ∧ acceleratedOrbit 12 1596 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1596 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1596) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1596.1, data_12_1596.2]

end Collatz.Research.StoppingAtlas.Batch0304
