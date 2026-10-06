import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0769

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4628. -/
theorem bounds_13_4628 : exactInterval 13 4628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4628 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4628) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4628 : oddCount 4628 13 = 4 ∧ acceleratedOrbit 13 4628 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4628 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4628) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4628.1, data_13_4628.2]

/-- Complete interval computation for depth 13, residue 4629. -/
theorem bounds_13_4629 : exactInterval 13 4629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4629 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4629) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4629 : oddCount 4629 13 = 4 ∧ acceleratedOrbit 13 4629 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4629 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4629) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4629.1, data_13_4629.2]

/-- Complete interval computation for depth 13, residue 4630. -/
theorem bounds_13_4630 : exactInterval 13 4630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4630 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4630) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4630 : oddCount 4630 13 = 6 ∧ acceleratedOrbit 13 4630 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4630 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4630) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4630.1, data_13_4630.2]

/-- Complete interval computation for depth 13, residue 4631. -/
theorem bounds_13_4631 : exactInterval 13 4631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4631 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4631) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4631 : oddCount 4631 13 = 6 ∧ acceleratedOrbit 13 4631 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4631 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4631) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4631.1, data_13_4631.2]

/-- Complete interval computation for depth 13, residue 4632. -/
theorem bounds_13_4632 : exactInterval 13 4632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4632 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4632) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4632 : oddCount 4632 13 = 4 ∧ acceleratedOrbit 13 4632 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4632 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4632) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4632.1, data_13_4632.2]

/-- Complete interval computation for depth 13, residue 4633. -/
theorem bounds_13_4633 : exactInterval 13 4633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4633 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4633) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4633 : oddCount 4633 13 = 6 ∧ acceleratedOrbit 13 4633 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4633 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4633) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4633.1, data_13_4633.2]

/-- Complete interval computation for depth 13, residue 4634. -/
theorem bounds_13_4634 : exactInterval 13 4634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4634 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4634) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4634 : oddCount 4634 13 = 4 ∧ acceleratedOrbit 13 4634 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4634 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4634) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4634.1, data_13_4634.2]

/-- Complete interval computation for depth 13, residue 4635. -/
theorem bounds_13_4635 : exactInterval 13 4635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4635 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4635) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4635 : oddCount 4635 13 = 9 ∧ acceleratedOrbit 13 4635 = 11141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4635 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4635) = 3 ^ 9 * m + 11141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4635.1, data_13_4635.2]

/-- Complete interval computation for depth 13, residue 4636. -/
theorem bounds_13_4636 : exactInterval 13 4636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4636 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4636) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4636 : oddCount 4636 13 = 7 ∧ acceleratedOrbit 13 4636 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4636 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4636) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4636.1, data_13_4636.2]

/-- Complete interval computation for depth 13, residue 4637. -/
theorem bounds_13_4637 : exactInterval 13 4637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4637 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4637) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4637 : oddCount 4637 13 = 7 ∧ acceleratedOrbit 13 4637 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4637 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4637) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4637.1, data_13_4637.2]

/-- Complete interval computation for depth 13, residue 4638. -/
theorem bounds_13_4638 : exactInterval 13 4638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4638 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4638) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4638 : oddCount 4638 13 = 7 ∧ acceleratedOrbit 13 4638 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4638 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4638) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4638.1, data_13_4638.2]

/-- Complete interval computation for depth 13, residue 4639. -/
theorem bounds_13_4639 : exactInterval 13 4639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4639 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4639) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4639 : oddCount 4639 13 = 9 ∧ acceleratedOrbit 13 4639 = 11150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4639 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4639) = 3 ^ 9 * m + 11150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4639.1, data_13_4639.2]

/-- Complete interval computation for depth 13, residue 4640. -/
theorem bounds_13_4640 : exactInterval 13 4640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4640 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4640) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4640 : oddCount 4640 13 = 4 ∧ acceleratedOrbit 13 4640 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4640 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4640) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4640.1, data_13_4640.2]

/-- Complete interval computation for depth 13, residue 4641. -/
theorem bounds_13_4641 : exactInterval 13 4641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4641 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4641) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4641 : oddCount 4641 13 = 7 ∧ acceleratedOrbit 13 4641 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4641 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4641) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4641.1, data_13_4641.2]

/-- Complete interval computation for depth 13, residue 4642. -/
theorem bounds_13_4642 : exactInterval 13 4642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4642 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4642) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4642 : oddCount 4642 13 = 4 ∧ acceleratedOrbit 13 4642 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4642 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4642) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4642.1, data_13_4642.2]

end Collatz.Research.StoppingAtlas.Batch0769
