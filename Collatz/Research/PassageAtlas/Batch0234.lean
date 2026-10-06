import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0234

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7634. -/
theorem bounds_15_7634 : exactInterval 15 7634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7634 : oddCount 7634 15 = 9 ∧ acceleratedOrbit 15 7634 = 4589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7634) = 3 ^ 9 * m + 4589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7634.1, data_15_7634.2]

/-- Complete interval computation for depth 15, residue 7635. -/
theorem bounds_15_7635 : exactInterval 15 7635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7635 : oddCount 7635 15 = 9 ∧ acceleratedOrbit 15 7635 = 4589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7635) = 3 ^ 9 * m + 4589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7635.1, data_15_7635.2]

/-- Complete interval computation for depth 15, residue 7636. -/
theorem bounds_15_7636 : exactInterval 15 7636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7636 : oddCount 7636 15 = 4 ∧ acceleratedOrbit 15 7636 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7636) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7636.1, data_15_7636.2]

/-- Complete interval computation for depth 15, residue 7637. -/
theorem bounds_15_7637 : exactInterval 15 7637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7637 : oddCount 7637 15 = 4 ∧ acceleratedOrbit 15 7637 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7637) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7637.1, data_15_7637.2]

/-- Complete interval computation for depth 15, residue 7638. -/
theorem bounds_15_7638 : exactInterval 15 7638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7638 : oddCount 7638 15 = 6 ∧ acceleratedOrbit 15 7638 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7638) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7638.1, data_15_7638.2]

/-- Complete interval computation for depth 15, residue 7639. -/
theorem bounds_15_7639 : exactInterval 15 7639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7639 : oddCount 7639 15 = 6 ∧ acceleratedOrbit 15 7639 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7639) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7639.1, data_15_7639.2]

/-- Complete interval computation for depth 15, residue 7640. -/
theorem bounds_15_7640 : exactInterval 15 7640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7640 : oddCount 7640 15 = 7 ∧ acceleratedOrbit 15 7640 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7640) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7640.1, data_15_7640.2]

/-- Complete interval computation for depth 15, residue 7641. -/
theorem bounds_15_7641 : exactInterval 15 7641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7641 : oddCount 7641 15 = 7 ∧ acceleratedOrbit 15 7641 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7641) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7641.1, data_15_7641.2]

/-- Complete interval computation for depth 15, residue 7642. -/
theorem bounds_15_7642 : exactInterval 15 7642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7642 : oddCount 7642 15 = 7 ∧ acceleratedOrbit 15 7642 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7642) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7642.1, data_15_7642.2]

/-- Complete interval computation for depth 15, residue 7643. -/
theorem bounds_15_7643 : exactInterval 15 7643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7643 : oddCount 7643 15 = 8 ∧ acceleratedOrbit 15 7643 = 1532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7643) = 3 ^ 8 * m + 1532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7643.1, data_15_7643.2]

/-- Complete interval computation for depth 15, residue 7644. -/
theorem bounds_15_7644 : exactInterval 15 7644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7644 : oddCount 7644 15 = 7 ∧ acceleratedOrbit 15 7644 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7644) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7644.1, data_15_7644.2]

/-- Complete interval computation for depth 15, residue 7645. -/
theorem bounds_15_7645 : exactInterval 15 7645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7645 : oddCount 7645 15 = 7 ∧ acceleratedOrbit 15 7645 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7645) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7645.1, data_15_7645.2]

/-- Complete interval computation for depth 15, residue 7646. -/
theorem bounds_15_7646 : exactInterval 15 7646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7646 : oddCount 7646 15 = 10 ∧ acceleratedOrbit 15 7646 = 13783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7646) = 3 ^ 10 * m + 13783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7646.1, data_15_7646.2]

/-- Complete interval computation for depth 15, residue 7647. -/
theorem bounds_15_7647 : exactInterval 15 7647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7647 : oddCount 7647 15 = 10 ∧ acceleratedOrbit 15 7647 = 13783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7647) = 3 ^ 10 * m + 13783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7647.1, data_15_7647.2]

/-- Complete interval computation for depth 15, residue 7648. -/
theorem bounds_15_7648 : exactInterval 15 7648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7648 : oddCount 7648 15 = 9 ∧ acceleratedOrbit 15 7648 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7648) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7648.1, data_15_7648.2]

/-- Complete interval computation for depth 15, residue 7649. -/
theorem bounds_15_7649 : exactInterval 15 7649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7649 : oddCount 7649 15 = 10 ∧ acceleratedOrbit 15 7649 = 13790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7649) = 3 ^ 10 * m + 13790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7649.1, data_15_7649.2]

/-- Complete interval computation for depth 15, residue 7650. -/
theorem bounds_15_7650 : exactInterval 15 7650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7650 : oddCount 7650 15 = 4 ∧ acceleratedOrbit 15 7650 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7650) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7650.1, data_15_7650.2]

/-- Complete interval computation for depth 15, residue 7651. -/
theorem bounds_15_7651 : exactInterval 15 7651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7651 : oddCount 7651 15 = 4 ∧ acceleratedOrbit 15 7651 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7651) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7651.1, data_15_7651.2]

/-- Complete interval computation for depth 15, residue 7652. -/
theorem bounds_15_7652 : exactInterval 15 7652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7652 : oddCount 7652 15 = 8 ∧ acceleratedOrbit 15 7652 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7652) = 3 ^ 8 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7652.1, data_15_7652.2]

/-- Complete interval computation for depth 15, residue 7653. -/
theorem bounds_15_7653 : exactInterval 15 7653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7653 : oddCount 7653 15 = 8 ∧ acceleratedOrbit 15 7653 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7653) = 3 ^ 8 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7653.1, data_15_7653.2]

/-- Complete interval computation for depth 15, residue 7654. -/
theorem bounds_15_7654 : exactInterval 15 7654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7654 : oddCount 7654 15 = 8 ∧ acceleratedOrbit 15 7654 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7654) = 3 ^ 8 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7654.1, data_15_7654.2]

/-- Complete interval computation for depth 15, residue 7655. -/
theorem bounds_15_7655 : exactInterval 15 7655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7655 : oddCount 7655 15 = 7 ∧ acceleratedOrbit 15 7655 = 511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7655) = 3 ^ 7 * m + 511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7655.1, data_15_7655.2]

/-- Complete interval computation for depth 15, residue 7656. -/
theorem bounds_15_7656 : exactInterval 15 7656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7656 : oddCount 7656 15 = 9 ∧ acceleratedOrbit 15 7656 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7656) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7656.1, data_15_7656.2]

/-- Complete interval computation for depth 15, residue 7657. -/
theorem bounds_15_7657 : exactInterval 15 7657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7657 : oddCount 7657 15 = 9 ∧ acceleratedOrbit 15 7657 = 4601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7657) = 3 ^ 9 * m + 4601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7657.1, data_15_7657.2]

/-- Complete interval computation for depth 15, residue 7658. -/
theorem bounds_15_7658 : exactInterval 15 7658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7658 : oddCount 7658 15 = 9 ∧ acceleratedOrbit 15 7658 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7658) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7658.1, data_15_7658.2]

/-- Complete interval computation for depth 15, residue 7659. -/
theorem bounds_15_7659 : exactInterval 15 7659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7659 : oddCount 7659 15 = 11 ∧ acceleratedOrbit 15 7659 = 41417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7659) = 3 ^ 11 * m + 41417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7659.1, data_15_7659.2]

/-- Complete interval computation for depth 15, residue 7660. -/
theorem bounds_15_7660 : exactInterval 15 7660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7660 : oddCount 7660 15 = 9 ∧ acceleratedOrbit 15 7660 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7660) = 3 ^ 9 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7660.1, data_15_7660.2]

/-- Complete interval computation for depth 15, residue 7661. -/
theorem bounds_15_7661 : exactInterval 15 7661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7661 : oddCount 7661 15 = 9 ∧ acceleratedOrbit 15 7661 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7661) = 3 ^ 9 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7661.1, data_15_7661.2]

/-- Complete interval computation for depth 15, residue 7662. -/
theorem bounds_15_7662 : exactInterval 15 7662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7662 : oddCount 7662 15 = 9 ∧ acceleratedOrbit 15 7662 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7662) = 3 ^ 9 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7662.1, data_15_7662.2]

/-- Complete interval computation for depth 15, residue 7663. -/
theorem bounds_15_7663 : exactInterval 15 7663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7663 : oddCount 7663 15 = 11 ∧ acceleratedOrbit 15 7663 = 41435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7663) = 3 ^ 11 * m + 41435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7663.1, data_15_7663.2]

/-- Complete interval computation for depth 15, residue 7664. -/
theorem bounds_15_7664 : exactInterval 15 7664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7664 : oddCount 7664 15 = 9 ∧ acceleratedOrbit 15 7664 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7664) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7664.1, data_15_7664.2]

/-- Complete interval computation for depth 15, residue 7665. -/
theorem bounds_15_7665 : exactInterval 15 7665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7665 : oddCount 7665 15 = 9 ∧ acceleratedOrbit 15 7665 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7665) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7665.1, data_15_7665.2]

/-- Complete interval computation for depth 15, residue 7666. -/
theorem bounds_15_7666 : exactInterval 15 7666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7666 : oddCount 7666 15 = 8 ∧ acceleratedOrbit 15 7666 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7666) = 3 ^ 8 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7666.1, data_15_7666.2]

end Collatz.Research.PassageAtlas.Batch0234
