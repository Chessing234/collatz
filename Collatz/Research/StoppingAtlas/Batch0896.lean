import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0896

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6579. -/
theorem bounds_13_6579 : exactInterval 13 6579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6579 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6579) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6579 : oddCount 6579 13 = 6 ∧ acceleratedOrbit 13 6579 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6579 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6579) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6579.1, data_13_6579.2]

/-- Complete interval computation for depth 13, residue 6580. -/
theorem bounds_13_6580 : exactInterval 13 6580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6580 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6580) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6580 : oddCount 6580 13 = 6 ∧ acceleratedOrbit 13 6580 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6580 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6580) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6580.1, data_13_6580.2]

/-- Complete interval computation for depth 13, residue 6581. -/
theorem bounds_13_6581 : exactInterval 13 6581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6581 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6581) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6581 : oddCount 6581 13 = 6 ∧ acceleratedOrbit 13 6581 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6581 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6581) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6581.1, data_13_6581.2]

/-- Complete interval computation for depth 13, residue 6582. -/
theorem bounds_13_6582 : exactInterval 13 6582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6582 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6582) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6582 : oddCount 6582 13 = 6 ∧ acceleratedOrbit 13 6582 = 586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6582 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6582) = 3 ^ 6 * m + 586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6582.1, data_13_6582.2]

/-- Complete interval computation for depth 13, residue 6583. -/
theorem bounds_13_6583 : exactInterval 13 6583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6583 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6583) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6583 : oddCount 6583 13 = 6 ∧ acceleratedOrbit 13 6583 = 586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6583 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6583) = 3 ^ 6 * m + 586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6583.1, data_13_6583.2]

/-- Complete interval computation for depth 13, residue 6584. -/
theorem bounds_13_6584 : exactInterval 13 6584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6584 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6584) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6584 : oddCount 6584 13 = 6 ∧ acceleratedOrbit 13 6584 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6584 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6584) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6584.1, data_13_6584.2]

/-- Complete interval computation for depth 13, residue 6585. -/
theorem bounds_13_6585 : exactInterval 13 6585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6585 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6585) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6585 : oddCount 6585 13 = 6 ∧ acceleratedOrbit 13 6585 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6585 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6585) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6585.1, data_13_6585.2]

/-- Complete interval computation for depth 13, residue 6586. -/
theorem bounds_13_6586 : exactInterval 13 6586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6586 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6586) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6586 : oddCount 6586 13 = 6 ∧ acceleratedOrbit 13 6586 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6586 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6586) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6586.1, data_13_6586.2]

/-- Complete interval computation for depth 13, residue 6587. -/
theorem bounds_13_6587 : exactInterval 13 6587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6587 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6587) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6587 : oddCount 6587 13 = 8 ∧ acceleratedOrbit 13 6587 = 5278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6587 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6587) = 3 ^ 8 * m + 5278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6587.1, data_13_6587.2]

/-- Complete interval computation for depth 13, residue 6588. -/
theorem bounds_13_6588 : exactInterval 13 6588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6588 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6588) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6588 : oddCount 6588 13 = 7 ∧ acceleratedOrbit 13 6588 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6588 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6588) = 3 ^ 7 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6588.1, data_13_6588.2]

/-- Complete interval computation for depth 13, residue 6589. -/
theorem bounds_13_6589 : exactInterval 13 6589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6589 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6589) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6589 : oddCount 6589 13 = 7 ∧ acceleratedOrbit 13 6589 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6589 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6589) = 3 ^ 7 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6589.1, data_13_6589.2]

/-- Complete interval computation for depth 13, residue 6590. -/
theorem bounds_13_6590 : exactInterval 13 6590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6590 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6590) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6590 : oddCount 6590 13 = 7 ∧ acceleratedOrbit 13 6590 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6590 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6590) = 3 ^ 7 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6590.1, data_13_6590.2]

/-- Complete interval computation for depth 13, residue 6591. -/
theorem bounds_13_6591 : exactInterval 13 6591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6591 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6591) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6591 : oddCount 6591 13 = 11 ∧ acceleratedOrbit 13 6591 = 142550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6591 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6591) = 3 ^ 11 * m + 142550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6591.1, data_13_6591.2]

/-- Complete interval computation for depth 13, residue 6592. -/
theorem bounds_13_6592 : exactInterval 13 6592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6592 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6592) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6592 : oddCount 6592 13 = 6 ∧ acceleratedOrbit 13 6592 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6592 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6592) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6592.1, data_13_6592.2]

/-- Complete interval computation for depth 13, residue 6593. -/
theorem bounds_13_6593 : exactInterval 13 6593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6593 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6593) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6593 : oddCount 6593 13 = 8 ∧ acceleratedOrbit 13 6593 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6593 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6593) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6593.1, data_13_6593.2]

end Collatz.Research.StoppingAtlas.Batch0896
