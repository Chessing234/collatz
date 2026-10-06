import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0964

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7623. -/
theorem bounds_13_7623 : exactInterval 13 7623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7623 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7623) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7623 : oddCount 7623 13 = 7 ∧ acceleratedOrbit 13 7623 = 2036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7623 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7623) = 3 ^ 7 * m + 2036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7623.1, data_13_7623.2]

/-- Complete interval computation for depth 13, residue 7624. -/
theorem bounds_13_7624 : exactInterval 13 7624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7624 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7624) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7624 : oddCount 7624 13 = 5 ∧ acceleratedOrbit 13 7624 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7624 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7624) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7624.1, data_13_7624.2]

/-- Complete interval computation for depth 13, residue 7625. -/
theorem bounds_13_7625 : exactInterval 13 7625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7625 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7625) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7625 : oddCount 7625 13 = 6 ∧ acceleratedOrbit 13 7625 = 679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7625 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7625) = 3 ^ 6 * m + 679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7625.1, data_13_7625.2]

/-- Complete interval computation for depth 13, residue 7626. -/
theorem bounds_13_7626 : exactInterval 13 7626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7626 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7626) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7626 : oddCount 7626 13 = 5 ∧ acceleratedOrbit 13 7626 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7626 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7626) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7626.1, data_13_7626.2]

/-- Complete interval computation for depth 13, residue 7627. -/
theorem bounds_13_7627 : exactInterval 13 7627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7627 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7627) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7627 : oddCount 7627 13 = 7 ∧ acceleratedOrbit 13 7627 = 2038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7627 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7627) = 3 ^ 7 * m + 2038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7627.1, data_13_7627.2]

/-- Complete interval computation for depth 13, residue 7628. -/
theorem bounds_13_7628 : exactInterval 13 7628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7628 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7628) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7628 : oddCount 7628 13 = 5 ∧ acceleratedOrbit 13 7628 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7628 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7628) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7628.1, data_13_7628.2]

/-- Complete interval computation for depth 13, residue 7629. -/
theorem bounds_13_7629 : exactInterval 13 7629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7629 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7629) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7629 : oddCount 7629 13 = 5 ∧ acceleratedOrbit 13 7629 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7629 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7629) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7629.1, data_13_7629.2]

/-- Complete interval computation for depth 13, residue 7630. -/
theorem bounds_13_7630 : exactInterval 13 7630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7630 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7630) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7630 : oddCount 7630 13 = 8 ∧ acceleratedOrbit 13 7630 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7630 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7630) = 3 ^ 8 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7630.1, data_13_7630.2]

/-- Complete interval computation for depth 13, residue 7631. -/
theorem bounds_13_7631 : exactInterval 13 7631 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7631 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7631) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7631 : oddCount 7631 13 = 8 ∧ acceleratedOrbit 13 7631 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7631 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7631) = 3 ^ 8 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7631.1, data_13_7631.2]

/-- Complete interval computation for depth 13, residue 7632. -/
theorem bounds_13_7632 : exactInterval 13 7632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7632 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7632) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7632 : oddCount 7632 13 = 4 ∧ acceleratedOrbit 13 7632 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7632 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7632) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7632.1, data_13_7632.2]

/-- Complete interval computation for depth 13, residue 7633. -/
theorem bounds_13_7633 : exactInterval 13 7633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7633 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7633) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7633 : oddCount 7633 13 = 5 ∧ acceleratedOrbit 13 7633 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7633 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7633) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7633.1, data_13_7633.2]

/-- Complete interval computation for depth 13, residue 7634. -/
theorem bounds_13_7634 : exactInterval 13 7634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7634 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7634) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7634 : oddCount 7634 13 = 7 ∧ acceleratedOrbit 13 7634 = 2039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7634 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7634) = 3 ^ 7 * m + 2039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7634.1, data_13_7634.2]

/-- Complete interval computation for depth 13, residue 7635. -/
theorem bounds_13_7635 : exactInterval 13 7635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7635 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7635) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7635 : oddCount 7635 13 = 7 ∧ acceleratedOrbit 13 7635 = 2039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7635 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7635) = 3 ^ 7 * m + 2039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7635.1, data_13_7635.2]

/-- Complete interval computation for depth 13, residue 7636. -/
theorem bounds_13_7636 : exactInterval 13 7636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7636 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7636) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7636 : oddCount 7636 13 = 4 ∧ acceleratedOrbit 13 7636 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7636 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7636) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7636.1, data_13_7636.2]

/-- Complete interval computation for depth 13, residue 7637. -/
theorem bounds_13_7637 : exactInterval 13 7637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7637 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7637) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7637 : oddCount 7637 13 = 4 ∧ acceleratedOrbit 13 7637 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7637 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7637) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7637.1, data_13_7637.2]

/-- Complete interval computation for depth 13, residue 7638. -/
theorem bounds_13_7638 : exactInterval 13 7638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7638 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7638) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7638 : oddCount 7638 13 = 6 ∧ acceleratedOrbit 13 7638 = 680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7638 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7638) = 3 ^ 6 * m + 680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7638.1, data_13_7638.2]

end Collatz.Research.StoppingAtlas.Batch0964
