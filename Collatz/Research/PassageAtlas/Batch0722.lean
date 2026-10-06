import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0722

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23625. -/
theorem bounds_15_23625 : exactInterval 15 23625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23625 : oddCount 23625 15 = 11 ∧ acceleratedOrbit 15 23625 = 127736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23625) = 3 ^ 11 * m + 127736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23625.1, data_15_23625.2]

/-- Complete interval computation for depth 15, residue 23626. -/
theorem bounds_15_23626 : exactInterval 15 23626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23626 : oddCount 23626 15 = 9 ∧ acceleratedOrbit 15 23626 = 14201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23626) = 3 ^ 9 * m + 14201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23626.1, data_15_23626.2]

/-- Complete interval computation for depth 15, residue 23627. -/
theorem bounds_15_23627 : exactInterval 15 23627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23627 : oddCount 23627 15 = 7 ∧ acceleratedOrbit 15 23627 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23627) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23627.1, data_15_23627.2]

/-- Complete interval computation for depth 15, residue 23628. -/
theorem bounds_15_23628 : exactInterval 15 23628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23628 : oddCount 23628 15 = 9 ∧ acceleratedOrbit 15 23628 = 14201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23628) = 3 ^ 9 * m + 14201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23628.1, data_15_23628.2]

/-- Complete interval computation for depth 15, residue 23629. -/
theorem bounds_15_23629 : exactInterval 15 23629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23629 : oddCount 23629 15 = 9 ∧ acceleratedOrbit 15 23629 = 14201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23629) = 3 ^ 9 * m + 14201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23629.1, data_15_23629.2]

/-- Complete interval computation for depth 15, residue 23630. -/
theorem bounds_15_23630 : exactInterval 15 23630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23630 : oddCount 23630 15 = 6 ∧ acceleratedOrbit 15 23630 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23630) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23630.1, data_15_23630.2]

/-- Complete interval computation for depth 15, residue 23631. -/
theorem bounds_15_23631 : exactInterval 15 23631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23631 : oddCount 23631 15 = 6 ∧ acceleratedOrbit 15 23631 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23631) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23631.1, data_15_23631.2]

/-- Complete interval computation for depth 15, residue 23632. -/
theorem bounds_15_23632 : exactInterval 15 23632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23632 : oddCount 23632 15 = 3 ∧ acceleratedOrbit 15 23632 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23632) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23632.1, data_15_23632.2]

/-- Complete interval computation for depth 15, residue 23633. -/
theorem bounds_15_23633 : exactInterval 15 23633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23633 : oddCount 23633 15 = 9 ∧ acceleratedOrbit 15 23633 = 14201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23633) = 3 ^ 9 * m + 14201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23633.1, data_15_23633.2]

/-- Complete interval computation for depth 15, residue 23634. -/
theorem bounds_15_23634 : exactInterval 15 23634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23634 : oddCount 23634 15 = 10 ∧ acceleratedOrbit 15 23634 = 42596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23634) = 3 ^ 10 * m + 42596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23634.1, data_15_23634.2]

/-- Complete interval computation for depth 15, residue 23635. -/
theorem bounds_15_23635 : exactInterval 15 23635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23635 : oddCount 23635 15 = 10 ∧ acceleratedOrbit 15 23635 = 42596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23635) = 3 ^ 10 * m + 42596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23635.1, data_15_23635.2]

/-- Complete interval computation for depth 15, residue 23636. -/
theorem bounds_15_23636 : exactInterval 15 23636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23636 : oddCount 23636 15 = 3 ∧ acceleratedOrbit 15 23636 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23636) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23636.1, data_15_23636.2]

/-- Complete interval computation for depth 15, residue 23637. -/
theorem bounds_15_23637 : exactInterval 15 23637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23637 : oddCount 23637 15 = 3 ∧ acceleratedOrbit 15 23637 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23637) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23637.1, data_15_23637.2]

/-- Complete interval computation for depth 15, residue 23638. -/
theorem bounds_15_23638 : exactInterval 15 23638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23638 : oddCount 23638 15 = 7 ∧ acceleratedOrbit 15 23638 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23638) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23638.1, data_15_23638.2]

/-- Complete interval computation for depth 15, residue 23639. -/
theorem bounds_15_23639 : exactInterval 15 23639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23639 : oddCount 23639 15 = 7 ∧ acceleratedOrbit 15 23639 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23639) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23639.1, data_15_23639.2]

/-- Complete interval computation for depth 15, residue 23640. -/
theorem bounds_15_23640 : exactInterval 15 23640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23640 : oddCount 23640 15 = 8 ∧ acceleratedOrbit 15 23640 = 4738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23640) = 3 ^ 8 * m + 4738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23640.1, data_15_23640.2]

/-- Complete interval computation for depth 15, residue 23641. -/
theorem bounds_15_23641 : exactInterval 15 23641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23641 : oddCount 23641 15 = 8 ∧ acceleratedOrbit 15 23641 = 4735 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23641) = 3 ^ 8 * m + 4735 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23641.1, data_15_23641.2]

/-- Complete interval computation for depth 15, residue 23642. -/
theorem bounds_15_23642 : exactInterval 15 23642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23642 : oddCount 23642 15 = 8 ∧ acceleratedOrbit 15 23642 = 4738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23642) = 3 ^ 8 * m + 4738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23642.1, data_15_23642.2]

/-- Complete interval computation for depth 15, residue 23643. -/
theorem bounds_15_23643 : exactInterval 15 23643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23643 : oddCount 23643 15 = 9 ∧ acceleratedOrbit 15 23643 = 14203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23643) = 3 ^ 9 * m + 14203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23643.1, data_15_23643.2]

/-- Complete interval computation for depth 15, residue 23644. -/
theorem bounds_15_23644 : exactInterval 15 23644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23644 : oddCount 23644 15 = 8 ∧ acceleratedOrbit 15 23644 = 4738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23644) = 3 ^ 8 * m + 4738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23644.1, data_15_23644.2]

/-- Complete interval computation for depth 15, residue 23645. -/
theorem bounds_15_23645 : exactInterval 15 23645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23645 : oddCount 23645 15 = 8 ∧ acceleratedOrbit 15 23645 = 4738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23645) = 3 ^ 8 * m + 4738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23645.1, data_15_23645.2]

/-- Complete interval computation for depth 15, residue 23646. -/
theorem bounds_15_23646 : exactInterval 15 23646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23646 : oddCount 23646 15 = 10 ∧ acceleratedOrbit 15 23646 = 42616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23646) = 3 ^ 10 * m + 42616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23646.1, data_15_23646.2]

/-- Complete interval computation for depth 15, residue 23647. -/
theorem bounds_15_23647 : exactInterval 15 23647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23647 : oddCount 23647 15 = 10 ∧ acceleratedOrbit 15 23647 = 42616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23647) = 3 ^ 10 * m + 42616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23647.1, data_15_23647.2]

/-- Complete interval computation for depth 15, residue 23648. -/
theorem bounds_15_23648 : exactInterval 15 23648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23648 : oddCount 23648 15 = 3 ∧ acceleratedOrbit 15 23648 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23648) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23648.1, data_15_23648.2]

/-- Complete interval computation for depth 15, residue 23649. -/
theorem bounds_15_23649 : exactInterval 15 23649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23649 : oddCount 23649 15 = 8 ∧ acceleratedOrbit 15 23649 = 4736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23649) = 3 ^ 8 * m + 4736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23649.1, data_15_23649.2]

/-- Complete interval computation for depth 15, residue 23650. -/
theorem bounds_15_23650 : exactInterval 15 23650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23650 : oddCount 23650 15 = 9 ∧ acceleratedOrbit 15 23650 = 14215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23650) = 3 ^ 9 * m + 14215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23650.1, data_15_23650.2]

/-- Complete interval computation for depth 15, residue 23651. -/
theorem bounds_15_23651 : exactInterval 15 23651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23651 : oddCount 23651 15 = 9 ∧ acceleratedOrbit 15 23651 = 14215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23651) = 3 ^ 9 * m + 14215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23651.1, data_15_23651.2]

/-- Complete interval computation for depth 15, residue 23652. -/
theorem bounds_15_23652 : exactInterval 15 23652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23652 : oddCount 23652 15 = 9 ∧ acceleratedOrbit 15 23652 = 14215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23652) = 3 ^ 9 * m + 14215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23652.1, data_15_23652.2]

/-- Complete interval computation for depth 15, residue 23653. -/
theorem bounds_15_23653 : exactInterval 15 23653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23653 : oddCount 23653 15 = 9 ∧ acceleratedOrbit 15 23653 = 14215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23653) = 3 ^ 9 * m + 14215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23653.1, data_15_23653.2]

/-- Complete interval computation for depth 15, residue 23654. -/
theorem bounds_15_23654 : exactInterval 15 23654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23654 : oddCount 23654 15 = 9 ∧ acceleratedOrbit 15 23654 = 14215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23654) = 3 ^ 9 * m + 14215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23654.1, data_15_23654.2]

/-- Complete interval computation for depth 15, residue 23655. -/
theorem bounds_15_23655 : exactInterval 15 23655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23655 : oddCount 23655 15 = 11 ∧ acceleratedOrbit 15 23655 = 127889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23655) = 3 ^ 11 * m + 127889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23655.1, data_15_23655.2]

/-- Complete interval computation for depth 15, residue 23656. -/
theorem bounds_15_23656 : exactInterval 15 23656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23656 : oddCount 23656 15 = 3 ∧ acceleratedOrbit 15 23656 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23656) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23656.1, data_15_23656.2]

/-- Complete interval computation for depth 15, residue 23657. -/
theorem bounds_15_23657 : exactInterval 15 23657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23657 : oddCount 23657 15 = 9 ∧ acceleratedOrbit 15 23657 = 14212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23657) = 3 ^ 9 * m + 14212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23657.1, data_15_23657.2]

end Collatz.Research.PassageAtlas.Batch0722
