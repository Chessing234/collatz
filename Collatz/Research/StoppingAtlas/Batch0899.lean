import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0899

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6625. -/
theorem bounds_13_6625 : exactInterval 13 6625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6625 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6625) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6625 : oddCount 6625 13 = 8 ∧ acceleratedOrbit 13 6625 = 5309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6625 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6625) = 3 ^ 8 * m + 5309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6625.1, data_13_6625.2]

/-- Complete interval computation for depth 13, residue 6626. -/
theorem bounds_13_6626 : exactInterval 13 6626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6626 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6626) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6626 : oddCount 6626 13 = 6 ∧ acceleratedOrbit 13 6626 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6626 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6626) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6626.1, data_13_6626.2]

/-- Complete interval computation for depth 13, residue 6627. -/
theorem bounds_13_6627 : exactInterval 13 6627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6627 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6627) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6627 : oddCount 6627 13 = 6 ∧ acceleratedOrbit 13 6627 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6627 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6627) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6627.1, data_13_6627.2]

/-- Complete interval computation for depth 13, residue 6628. -/
theorem bounds_13_6628 : exactInterval 13 6628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6628 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6628) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6628 : oddCount 6628 13 = 7 ∧ acceleratedOrbit 13 6628 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6628 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6628) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6628.1, data_13_6628.2]

/-- Complete interval computation for depth 13, residue 6629. -/
theorem bounds_13_6629 : exactInterval 13 6629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6629 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6629) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6629 : oddCount 6629 13 = 7 ∧ acceleratedOrbit 13 6629 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6629 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6629) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6629.1, data_13_6629.2]

/-- Complete interval computation for depth 13, residue 6630. -/
theorem bounds_13_6630 : exactInterval 13 6630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6630 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6630) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6630 : oddCount 6630 13 = 7 ∧ acceleratedOrbit 13 6630 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6630 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6630) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6630.1, data_13_6630.2]

/-- Complete interval computation for depth 13, residue 6631. -/
theorem bounds_13_6631 : exactInterval 13 6631 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6631 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6631) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6631 : oddCount 6631 13 = 8 ∧ acceleratedOrbit 13 6631 = 5312 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6631 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6631) = 3 ^ 8 * m + 5312 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6631.1, data_13_6631.2]

/-- Complete interval computation for depth 13, residue 6632. -/
theorem bounds_13_6632 : exactInterval 13 6632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6632 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6632) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6632 : oddCount 6632 13 = 6 ∧ acceleratedOrbit 13 6632 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6632 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6632) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6632.1, data_13_6632.2]

/-- Complete interval computation for depth 13, residue 6633. -/
theorem bounds_13_6633 : exactInterval 13 6633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6633 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6633) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6633 : oddCount 6633 13 = 8 ∧ acceleratedOrbit 13 6633 = 5314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6633 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6633) = 3 ^ 8 * m + 5314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6633.1, data_13_6633.2]

/-- Complete interval computation for depth 13, residue 6634. -/
theorem bounds_13_6634 : exactInterval 13 6634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6634 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6634) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6634 : oddCount 6634 13 = 6 ∧ acceleratedOrbit 13 6634 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6634 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6634) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6634.1, data_13_6634.2]

/-- Complete interval computation for depth 13, residue 6635. -/
theorem bounds_13_6635 : exactInterval 13 6635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6635 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6635) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6635 : oddCount 6635 13 = 9 ∧ acceleratedOrbit 13 6635 = 15947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6635 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6635) = 3 ^ 9 * m + 15947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6635.1, data_13_6635.2]

/-- Complete interval computation for depth 13, residue 6636. -/
theorem bounds_13_6636 : exactInterval 13 6636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6636 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6636) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6636 : oddCount 6636 13 = 5 ∧ acceleratedOrbit 13 6636 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6636 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6636) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6636.1, data_13_6636.2]

/-- Complete interval computation for depth 13, residue 6637. -/
theorem bounds_13_6637 : exactInterval 13 6637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6637 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6637) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6637 : oddCount 6637 13 = 5 ∧ acceleratedOrbit 13 6637 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6637 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6637) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6637.1, data_13_6637.2]

/-- Complete interval computation for depth 13, residue 6638. -/
theorem bounds_13_6638 : exactInterval 13 6638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6638 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6638) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6638 : oddCount 6638 13 = 5 ∧ acceleratedOrbit 13 6638 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6638 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6638) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6638.1, data_13_6638.2]

/-- Complete interval computation for depth 13, residue 6639. -/
theorem bounds_13_6639 : exactInterval 13 6639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6639 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6639) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6639 : oddCount 6639 13 = 10 ∧ acceleratedOrbit 13 6639 = 47864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6639 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6639) = 3 ^ 10 * m + 47864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6639.1, data_13_6639.2]

end Collatz.Research.StoppingAtlas.Batch0899
