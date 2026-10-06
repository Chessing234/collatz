import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0831

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5580. -/
theorem bounds_13_5580 : exactInterval 13 5580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5580 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5580) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5580 : oddCount 5580 13 = 5 ∧ acceleratedOrbit 13 5580 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5580 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5580) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5580.1, data_13_5580.2]

/-- Complete interval computation for depth 13, residue 5581. -/
theorem bounds_13_5581 : exactInterval 13 5581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5581 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5581) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5581 : oddCount 5581 13 = 5 ∧ acceleratedOrbit 13 5581 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5581 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5581) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5581.1, data_13_5581.2]

/-- Complete interval computation for depth 13, residue 5582. -/
theorem bounds_13_5582 : exactInterval 13 5582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5582 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5582) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5582 : oddCount 5582 13 = 10 ∧ acceleratedOrbit 13 5582 = 40256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5582 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5582) = 3 ^ 10 * m + 40256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5582.1, data_13_5582.2]

/-- Complete interval computation for depth 13, residue 5583. -/
theorem bounds_13_5583 : exactInterval 13 5583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5583 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5583) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5583 : oddCount 5583 13 = 10 ∧ acceleratedOrbit 13 5583 = 40256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5583 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5583) = 3 ^ 10 * m + 40256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5583.1, data_13_5583.2]

/-- Complete interval computation for depth 13, residue 5584. -/
theorem bounds_13_5584 : exactInterval 13 5584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5584 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5584) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5584 : oddCount 5584 13 = 4 ∧ acceleratedOrbit 13 5584 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5584 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5584) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5584.1, data_13_5584.2]

/-- Complete interval computation for depth 13, residue 5585. -/
theorem bounds_13_5585 : exactInterval 13 5585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5585 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5585) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5585 : oddCount 5585 13 = 5 ∧ acceleratedOrbit 13 5585 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5585 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5585) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5585.1, data_13_5585.2]

/-- Complete interval computation for depth 13, residue 5586. -/
theorem bounds_13_5586 : exactInterval 13 5586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5586 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5586) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5586 : oddCount 5586 13 = 8 ∧ acceleratedOrbit 13 5586 = 4477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5586 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5586) = 3 ^ 8 * m + 4477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5586.1, data_13_5586.2]

/-- Complete interval computation for depth 13, residue 5587. -/
theorem bounds_13_5587 : exactInterval 13 5587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5587 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5587) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5587 : oddCount 5587 13 = 8 ∧ acceleratedOrbit 13 5587 = 4477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5587 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5587) = 3 ^ 8 * m + 4477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5587.1, data_13_5587.2]

/-- Complete interval computation for depth 13, residue 5588. -/
theorem bounds_13_5588 : exactInterval 13 5588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5588 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5588) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5588 : oddCount 5588 13 = 4 ∧ acceleratedOrbit 13 5588 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5588 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5588) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5588.1, data_13_5588.2]

/-- Complete interval computation for depth 13, residue 5589. -/
theorem bounds_13_5589 : exactInterval 13 5589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5589 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5589) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5589 : oddCount 5589 13 = 4 ∧ acceleratedOrbit 13 5589 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5589 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5589) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5589.1, data_13_5589.2]

/-- Complete interval computation for depth 13, residue 5590. -/
theorem bounds_13_5590 : exactInterval 13 5590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5590 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5590) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5590 : oddCount 5590 13 = 8 ∧ acceleratedOrbit 13 5590 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5590 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5590) = 3 ^ 8 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5590.1, data_13_5590.2]

/-- Complete interval computation for depth 13, residue 5591. -/
theorem bounds_13_5591 : exactInterval 13 5591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5591 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5591) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5591 : oddCount 5591 13 = 8 ∧ acceleratedOrbit 13 5591 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5591 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5591) = 3 ^ 8 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5591.1, data_13_5591.2]

/-- Complete interval computation for depth 13, residue 5592. -/
theorem bounds_13_5592 : exactInterval 13 5592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5592 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5592) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5592 : oddCount 5592 13 = 6 ∧ acceleratedOrbit 13 5592 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5592 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5592) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5592.1, data_13_5592.2]

/-- Complete interval computation for depth 13, residue 5593. -/
theorem bounds_13_5593 : exactInterval 13 5593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5593 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5593) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5593 : oddCount 5593 13 = 6 ∧ acceleratedOrbit 13 5593 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5593 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5593) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5593.1, data_13_5593.2]

/-- Complete interval computation for depth 13, residue 5594. -/
theorem bounds_13_5594 : exactInterval 13 5594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5594 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5594) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5594 : oddCount 5594 13 = 6 ∧ acceleratedOrbit 13 5594 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5594 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5594) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5594.1, data_13_5594.2]

/-- Complete interval computation for depth 13, residue 5595. -/
theorem bounds_13_5595 : exactInterval 13 5595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5595 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5595) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5595 : oddCount 5595 13 = 5 ∧ acceleratedOrbit 13 5595 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5595 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5595) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5595.1, data_13_5595.2]

end Collatz.Research.StoppingAtlas.Batch0831
