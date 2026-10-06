import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0661

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21626. -/
theorem bounds_15_21626 : exactInterval 15 21626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21626 : oddCount 21626 15 = 8 ∧ acceleratedOrbit 15 21626 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21626) = 3 ^ 8 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21626.1, data_15_21626.2]

/-- Complete interval computation for depth 15, residue 21627. -/
theorem bounds_15_21627 : exactInterval 15 21627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21627 : oddCount 21627 15 = 8 ∧ acceleratedOrbit 15 21627 = 4331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21627) = 3 ^ 8 * m + 4331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21627.1, data_15_21627.2]

/-- Complete interval computation for depth 15, residue 21628. -/
theorem bounds_15_21628 : exactInterval 15 21628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21628 : oddCount 21628 15 = 7 ∧ acceleratedOrbit 15 21628 = 1444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21628) = 3 ^ 7 * m + 1444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21628.1, data_15_21628.2]

/-- Complete interval computation for depth 15, residue 21629. -/
theorem bounds_15_21629 : exactInterval 15 21629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21629 : oddCount 21629 15 = 7 ∧ acceleratedOrbit 15 21629 = 1444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21629) = 3 ^ 7 * m + 1444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21629.1, data_15_21629.2]

/-- Complete interval computation for depth 15, residue 21630. -/
theorem bounds_15_21630 : exactInterval 15 21630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21630 : oddCount 21630 15 = 7 ∧ acceleratedOrbit 15 21630 = 1444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21630) = 3 ^ 7 * m + 1444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21630.1, data_15_21630.2]

/-- Complete interval computation for depth 15, residue 21631. -/
theorem bounds_15_21631 : exactInterval 15 21631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21631 : oddCount 21631 15 = 12 ∧ acceleratedOrbit 15 21631 = 350837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21631) = 3 ^ 12 * m + 350837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21631.1, data_15_21631.2]

/-- Complete interval computation for depth 15, residue 21632. -/
theorem bounds_15_21632 : exactInterval 15 21632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21632 : oddCount 21632 15 = 7 ∧ acceleratedOrbit 15 21632 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21632) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21632.1, data_15_21632.2]

/-- Complete interval computation for depth 15, residue 21633. -/
theorem bounds_15_21633 : exactInterval 15 21633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21633 : oddCount 21633 15 = 9 ∧ acceleratedOrbit 15 21633 = 12997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21633) = 3 ^ 9 * m + 12997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21633.1, data_15_21633.2]

/-- Complete interval computation for depth 15, residue 21634. -/
theorem bounds_15_21634 : exactInterval 15 21634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21634 : oddCount 21634 15 = 5 ∧ acceleratedOrbit 15 21634 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21634) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21634.1, data_15_21634.2]

/-- Complete interval computation for depth 15, residue 21635. -/
theorem bounds_15_21635 : exactInterval 15 21635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21635 : oddCount 21635 15 = 5 ∧ acceleratedOrbit 15 21635 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21635) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21635.1, data_15_21635.2]

/-- Complete interval computation for depth 15, residue 21636. -/
theorem bounds_15_21636 : exactInterval 15 21636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21636 : oddCount 21636 15 = 5 ∧ acceleratedOrbit 15 21636 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21636) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21636.1, data_15_21636.2]

/-- Complete interval computation for depth 15, residue 21637. -/
theorem bounds_15_21637 : exactInterval 15 21637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21637 : oddCount 21637 15 = 5 ∧ acceleratedOrbit 15 21637 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21637) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21637.1, data_15_21637.2]

/-- Complete interval computation for depth 15, residue 21638. -/
theorem bounds_15_21638 : exactInterval 15 21638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21638 : oddCount 21638 15 = 5 ∧ acceleratedOrbit 15 21638 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21638) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21638.1, data_15_21638.2]

/-- Complete interval computation for depth 15, residue 21639. -/
theorem bounds_15_21639 : exactInterval 15 21639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21639 : oddCount 21639 15 = 10 ∧ acceleratedOrbit 15 21639 = 39001 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21639) = 3 ^ 10 * m + 39001 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21639.1, data_15_21639.2]

/-- Complete interval computation for depth 15, residue 21640. -/
theorem bounds_15_21640 : exactInterval 15 21640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21640 : oddCount 21640 15 = 7 ∧ acceleratedOrbit 15 21640 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21640) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21640.1, data_15_21640.2]

/-- Complete interval computation for depth 15, residue 21641. -/
theorem bounds_15_21641 : exactInterval 15 21641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21641 : oddCount 21641 15 = 12 ∧ acceleratedOrbit 15 21641 = 351013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21641) = 3 ^ 12 * m + 351013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21641.1, data_15_21641.2]

/-- Complete interval computation for depth 15, residue 21642. -/
theorem bounds_15_21642 : exactInterval 15 21642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21642 : oddCount 21642 15 = 7 ∧ acceleratedOrbit 15 21642 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21642) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21642.1, data_15_21642.2]

/-- Complete interval computation for depth 15, residue 21643. -/
theorem bounds_15_21643 : exactInterval 15 21643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21643 : oddCount 21643 15 = 9 ∧ acceleratedOrbit 15 21643 = 13004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21643) = 3 ^ 9 * m + 13004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21643.1, data_15_21643.2]

/-- Complete interval computation for depth 15, residue 21644. -/
theorem bounds_15_21644 : exactInterval 15 21644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21644 : oddCount 21644 15 = 7 ∧ acceleratedOrbit 15 21644 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21644) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21644.1, data_15_21644.2]

/-- Complete interval computation for depth 15, residue 21645. -/
theorem bounds_15_21645 : exactInterval 15 21645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21645 : oddCount 21645 15 = 7 ∧ acceleratedOrbit 15 21645 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21645) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21645.1, data_15_21645.2]

/-- Complete interval computation for depth 15, residue 21646. -/
theorem bounds_15_21646 : exactInterval 15 21646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21646 : oddCount 21646 15 = 7 ∧ acceleratedOrbit 15 21646 = 1445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21646) = 3 ^ 7 * m + 1445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21646.1, data_15_21646.2]

/-- Complete interval computation for depth 15, residue 21647. -/
theorem bounds_15_21647 : exactInterval 15 21647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21647 : oddCount 21647 15 = 7 ∧ acceleratedOrbit 15 21647 = 1445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21647) = 3 ^ 7 * m + 1445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21647.1, data_15_21647.2]

/-- Complete interval computation for depth 15, residue 21648. -/
theorem bounds_15_21648 : exactInterval 15 21648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21648 : oddCount 21648 15 = 7 ∧ acceleratedOrbit 15 21648 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21648) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21648.1, data_15_21648.2]

/-- Complete interval computation for depth 15, residue 21649. -/
theorem bounds_15_21649 : exactInterval 15 21649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21649 : oddCount 21649 15 = 8 ∧ acceleratedOrbit 15 21649 = 4337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21649) = 3 ^ 8 * m + 4337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21649.1, data_15_21649.2]

/-- Complete interval computation for depth 15, residue 21650. -/
theorem bounds_15_21650 : exactInterval 15 21650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21650 : oddCount 21650 15 = 8 ∧ acceleratedOrbit 15 21650 = 4337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21650) = 3 ^ 8 * m + 4337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21650.1, data_15_21650.2]

/-- Complete interval computation for depth 15, residue 21651. -/
theorem bounds_15_21651 : exactInterval 15 21651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21651 : oddCount 21651 15 = 8 ∧ acceleratedOrbit 15 21651 = 4337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21651) = 3 ^ 8 * m + 4337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21651.1, data_15_21651.2]

/-- Complete interval computation for depth 15, residue 21652. -/
theorem bounds_15_21652 : exactInterval 15 21652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21652 : oddCount 21652 15 = 7 ∧ acceleratedOrbit 15 21652 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21652) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21652.1, data_15_21652.2]

/-- Complete interval computation for depth 15, residue 21653. -/
theorem bounds_15_21653 : exactInterval 15 21653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21653 : oddCount 21653 15 = 7 ∧ acceleratedOrbit 15 21653 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21653) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21653.1, data_15_21653.2]

/-- Complete interval computation for depth 15, residue 21654. -/
theorem bounds_15_21654 : exactInterval 15 21654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21654 : oddCount 21654 15 = 7 ∧ acceleratedOrbit 15 21654 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21654) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21654.1, data_15_21654.2]

/-- Complete interval computation for depth 15, residue 21655. -/
theorem bounds_15_21655 : exactInterval 15 21655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21655 : oddCount 21655 15 = 7 ∧ acceleratedOrbit 15 21655 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21655) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21655.1, data_15_21655.2]

/-- Complete interval computation for depth 15, residue 21656. -/
theorem bounds_15_21656 : exactInterval 15 21656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21656 : oddCount 21656 15 = 7 ∧ acceleratedOrbit 15 21656 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21656) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21656.1, data_15_21656.2]

/-- Complete interval computation for depth 15, residue 21657. -/
theorem bounds_15_21657 : exactInterval 15 21657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21657 : oddCount 21657 15 = 6 ∧ acceleratedOrbit 15 21657 = 482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21657) = 3 ^ 6 * m + 482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21657.1, data_15_21657.2]

/-- Complete interval computation for depth 15, residue 21658. -/
theorem bounds_15_21658 : exactInterval 15 21658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21658 : oddCount 21658 15 = 7 ∧ acceleratedOrbit 15 21658 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21658) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21658.1, data_15_21658.2]

end Collatz.Research.PassageAtlas.Batch0661
