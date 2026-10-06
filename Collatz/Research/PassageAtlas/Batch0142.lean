import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0142

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4620. -/
theorem bounds_15_4620 : exactInterval 15 4620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4620 : oddCount 4620 15 = 5 ∧ acceleratedOrbit 15 4620 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4620) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4620.1, data_15_4620.2]

/-- Complete interval computation for depth 15, residue 4621. -/
theorem bounds_15_4621 : exactInterval 15 4621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4621 : oddCount 4621 15 = 5 ∧ acceleratedOrbit 15 4621 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4621) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4621.1, data_15_4621.2]

/-- Complete interval computation for depth 15, residue 4622. -/
theorem bounds_15_4622 : exactInterval 15 4622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4622 : oddCount 4622 15 = 9 ∧ acceleratedOrbit 15 4622 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4622) = 3 ^ 9 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4622.1, data_15_4622.2]

/-- Complete interval computation for depth 15, residue 4623. -/
theorem bounds_15_4623 : exactInterval 15 4623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4623 : oddCount 4623 15 = 9 ∧ acceleratedOrbit 15 4623 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4623) = 3 ^ 9 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4623.1, data_15_4623.2]

/-- Complete interval computation for depth 15, residue 4624. -/
theorem bounds_15_4624 : exactInterval 15 4624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4624 : oddCount 4624 15 = 5 ∧ acceleratedOrbit 15 4624 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4624) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4624.1, data_15_4624.2]

/-- Complete interval computation for depth 15, residue 4625. -/
theorem bounds_15_4625 : exactInterval 15 4625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4625 : oddCount 4625 15 = 5 ∧ acceleratedOrbit 15 4625 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4625) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4625.1, data_15_4625.2]

/-- Complete interval computation for depth 15, residue 4626. -/
theorem bounds_15_4626 : exactInterval 15 4626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4626 : oddCount 4626 15 = 6 ∧ acceleratedOrbit 15 4626 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4626) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4626.1, data_15_4626.2]

/-- Complete interval computation for depth 15, residue 4627. -/
theorem bounds_15_4627 : exactInterval 15 4627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4627 : oddCount 4627 15 = 6 ∧ acceleratedOrbit 15 4627 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4627) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4627.1, data_15_4627.2]

/-- Complete interval computation for depth 15, residue 4628. -/
theorem bounds_15_4628 : exactInterval 15 4628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4628 : oddCount 4628 15 = 5 ∧ acceleratedOrbit 15 4628 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4628) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4628.1, data_15_4628.2]

/-- Complete interval computation for depth 15, residue 4629. -/
theorem bounds_15_4629 : exactInterval 15 4629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4629 : oddCount 4629 15 = 5 ∧ acceleratedOrbit 15 4629 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4629) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4629.1, data_15_4629.2]

/-- Complete interval computation for depth 15, residue 4630. -/
theorem bounds_15_4630 : exactInterval 15 4630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4630 : oddCount 4630 15 = 7 ∧ acceleratedOrbit 15 4630 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4630) = 3 ^ 7 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4630.1, data_15_4630.2]

/-- Complete interval computation for depth 15, residue 4631. -/
theorem bounds_15_4631 : exactInterval 15 4631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4631 : oddCount 4631 15 = 7 ∧ acceleratedOrbit 15 4631 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4631) = 3 ^ 7 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4631.1, data_15_4631.2]

/-- Complete interval computation for depth 15, residue 4632. -/
theorem bounds_15_4632 : exactInterval 15 4632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4632 : oddCount 4632 15 = 5 ∧ acceleratedOrbit 15 4632 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4632) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4632.1, data_15_4632.2]

/-- Complete interval computation for depth 15, residue 4633. -/
theorem bounds_15_4633 : exactInterval 15 4633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4633 : oddCount 4633 15 = 7 ∧ acceleratedOrbit 15 4633 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4633) = 3 ^ 7 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4633.1, data_15_4633.2]

/-- Complete interval computation for depth 15, residue 4634. -/
theorem bounds_15_4634 : exactInterval 15 4634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4634 : oddCount 4634 15 = 5 ∧ acceleratedOrbit 15 4634 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4634) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4634.1, data_15_4634.2]

/-- Complete interval computation for depth 15, residue 4635. -/
theorem bounds_15_4635 : exactInterval 15 4635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4635 : oddCount 4635 15 = 10 ∧ acceleratedOrbit 15 4635 = 8356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4635) = 3 ^ 10 * m + 8356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4635.1, data_15_4635.2]

/-- Complete interval computation for depth 15, residue 4636. -/
theorem bounds_15_4636 : exactInterval 15 4636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4636 : oddCount 4636 15 = 8 ∧ acceleratedOrbit 15 4636 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4636) = 3 ^ 8 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4636.1, data_15_4636.2]

/-- Complete interval computation for depth 15, residue 4637. -/
theorem bounds_15_4637 : exactInterval 15 4637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4637 : oddCount 4637 15 = 8 ∧ acceleratedOrbit 15 4637 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4637) = 3 ^ 8 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4637.1, data_15_4637.2]

/-- Complete interval computation for depth 15, residue 4638. -/
theorem bounds_15_4638 : exactInterval 15 4638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4638 : oddCount 4638 15 = 8 ∧ acceleratedOrbit 15 4638 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4638) = 3 ^ 8 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4638.1, data_15_4638.2]

/-- Complete interval computation for depth 15, residue 4639. -/
theorem bounds_15_4639 : exactInterval 15 4639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4639 : oddCount 4639 15 = 10 ∧ acceleratedOrbit 15 4639 = 8363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4639) = 3 ^ 10 * m + 8363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4639.1, data_15_4639.2]

/-- Complete interval computation for depth 15, residue 4640. -/
theorem bounds_15_4640 : exactInterval 15 4640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4640 : oddCount 4640 15 = 6 ∧ acceleratedOrbit 15 4640 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4640) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4640.1, data_15_4640.2]

/-- Complete interval computation for depth 15, residue 4641. -/
theorem bounds_15_4641 : exactInterval 15 4641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4641 : oddCount 4641 15 = 8 ∧ acceleratedOrbit 15 4641 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4641) = 3 ^ 8 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4641.1, data_15_4641.2]

/-- Complete interval computation for depth 15, residue 4642. -/
theorem bounds_15_4642 : exactInterval 15 4642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4642 : oddCount 4642 15 = 5 ∧ acceleratedOrbit 15 4642 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4642) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4642.1, data_15_4642.2]

/-- Complete interval computation for depth 15, residue 4643. -/
theorem bounds_15_4643 : exactInterval 15 4643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4643 : oddCount 4643 15 = 5 ∧ acceleratedOrbit 15 4643 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4643) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4643.1, data_15_4643.2]

/-- Complete interval computation for depth 15, residue 4644. -/
theorem bounds_15_4644 : exactInterval 15 4644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4644 : oddCount 4644 15 = 10 ∧ acceleratedOrbit 15 4644 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4644) = 3 ^ 10 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4644.1, data_15_4644.2]

/-- Complete interval computation for depth 15, residue 4645. -/
theorem bounds_15_4645 : exactInterval 15 4645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4645 : oddCount 4645 15 = 10 ∧ acceleratedOrbit 15 4645 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4645) = 3 ^ 10 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4645.1, data_15_4645.2]

/-- Complete interval computation for depth 15, residue 4646. -/
theorem bounds_15_4646 : exactInterval 15 4646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4646 : oddCount 4646 15 = 10 ∧ acceleratedOrbit 15 4646 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4646) = 3 ^ 10 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4646.1, data_15_4646.2]

/-- Complete interval computation for depth 15, residue 4647. -/
theorem bounds_15_4647 : exactInterval 15 4647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4647 : oddCount 4647 15 = 9 ∧ acceleratedOrbit 15 4647 = 2794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4647) = 3 ^ 9 * m + 2794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4647.1, data_15_4647.2]

/-- Complete interval computation for depth 15, residue 4648. -/
theorem bounds_15_4648 : exactInterval 15 4648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4648 : oddCount 4648 15 = 6 ∧ acceleratedOrbit 15 4648 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4648) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4648.1, data_15_4648.2]

/-- Complete interval computation for depth 15, residue 4649. -/
theorem bounds_15_4649 : exactInterval 15 4649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4649 : oddCount 4649 15 = 10 ∧ acceleratedOrbit 15 4649 = 8381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4649) = 3 ^ 10 * m + 8381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4649.1, data_15_4649.2]

/-- Complete interval computation for depth 15, residue 4650. -/
theorem bounds_15_4650 : exactInterval 15 4650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4650 : oddCount 4650 15 = 6 ∧ acceleratedOrbit 15 4650 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4650) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4650.1, data_15_4650.2]

/-- Complete interval computation for depth 15, residue 4651. -/
theorem bounds_15_4651 : exactInterval 15 4651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4651 : oddCount 4651 15 = 5 ∧ acceleratedOrbit 15 4651 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4651) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4651.1, data_15_4651.2]

/-- Complete interval computation for depth 15, residue 4652. -/
theorem bounds_15_4652 : exactInterval 15 4652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4652 : oddCount 4652 15 = 8 ∧ acceleratedOrbit 15 4652 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4652) = 3 ^ 8 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4652.1, data_15_4652.2]

end Collatz.Research.PassageAtlas.Batch0142
