import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0844

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27623. -/
theorem bounds_15_27623 : exactInterval 15 27623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27623 : oddCount 27623 15 = 9 ∧ acceleratedOrbit 15 27623 = 16595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27623) = 3 ^ 9 * m + 16595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27623.1, data_15_27623.2]

/-- Complete interval computation for depth 15, residue 27624. -/
theorem bounds_15_27624 : exactInterval 15 27624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27624 : oddCount 27624 15 = 5 ∧ acceleratedOrbit 15 27624 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27624) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27624.1, data_15_27624.2]

/-- Complete interval computation for depth 15, residue 27625. -/
theorem bounds_15_27625 : exactInterval 15 27625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27625 : oddCount 27625 15 = 11 ∧ acceleratedOrbit 15 27625 = 149354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27625) = 3 ^ 11 * m + 149354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27625.1, data_15_27625.2]

/-- Complete interval computation for depth 15, residue 27626. -/
theorem bounds_15_27626 : exactInterval 15 27626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27626 : oddCount 27626 15 = 5 ∧ acceleratedOrbit 15 27626 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27626) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27626.1, data_15_27626.2]

/-- Complete interval computation for depth 15, residue 27627. -/
theorem bounds_15_27627 : exactInterval 15 27627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27627 : oddCount 27627 15 = 7 ∧ acceleratedOrbit 15 27627 = 1844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27627) = 3 ^ 7 * m + 1844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27627.1, data_15_27627.2]

/-- Complete interval computation for depth 15, residue 27628. -/
theorem bounds_15_27628 : exactInterval 15 27628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27628 : oddCount 27628 15 = 9 ∧ acceleratedOrbit 15 27628 = 16600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27628) = 3 ^ 9 * m + 16600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27628.1, data_15_27628.2]

/-- Complete interval computation for depth 15, residue 27629. -/
theorem bounds_15_27629 : exactInterval 15 27629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27629 : oddCount 27629 15 = 9 ∧ acceleratedOrbit 15 27629 = 16600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27629) = 3 ^ 9 * m + 16600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27629.1, data_15_27629.2]

/-- Complete interval computation for depth 15, residue 27630. -/
theorem bounds_15_27630 : exactInterval 15 27630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27630 : oddCount 27630 15 = 9 ∧ acceleratedOrbit 15 27630 = 16600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27630) = 3 ^ 9 * m + 16600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27630.1, data_15_27630.2]

/-- Complete interval computation for depth 15, residue 27631. -/
theorem bounds_15_27631 : exactInterval 15 27631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27631 : oddCount 27631 15 = 11 ∧ acceleratedOrbit 15 27631 = 149384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27631) = 3 ^ 11 * m + 149384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27631.1, data_15_27631.2]

/-- Complete interval computation for depth 15, residue 27632. -/
theorem bounds_15_27632 : exactInterval 15 27632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27632 : oddCount 27632 15 = 8 ∧ acceleratedOrbit 15 27632 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27632) = 3 ^ 8 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27632.1, data_15_27632.2]

/-- Complete interval computation for depth 15, residue 27633. -/
theorem bounds_15_27633 : exactInterval 15 27633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27633 : oddCount 27633 15 = 5 ∧ acceleratedOrbit 15 27633 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27633) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27633.1, data_15_27633.2]

/-- Complete interval computation for depth 15, residue 27634. -/
theorem bounds_15_27634 : exactInterval 15 27634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27634 : oddCount 27634 15 = 9 ∧ acceleratedOrbit 15 27634 = 16604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27634) = 3 ^ 9 * m + 16604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27634.1, data_15_27634.2]

/-- Complete interval computation for depth 15, residue 27635. -/
theorem bounds_15_27635 : exactInterval 15 27635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27635 : oddCount 27635 15 = 9 ∧ acceleratedOrbit 15 27635 = 16604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27635) = 3 ^ 9 * m + 16604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27635.1, data_15_27635.2]

/-- Complete interval computation for depth 15, residue 27636. -/
theorem bounds_15_27636 : exactInterval 15 27636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27636 : oddCount 27636 15 = 8 ∧ acceleratedOrbit 15 27636 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27636) = 3 ^ 8 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27636.1, data_15_27636.2]

/-- Complete interval computation for depth 15, residue 27637. -/
theorem bounds_15_27637 : exactInterval 15 27637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27637 : oddCount 27637 15 = 8 ∧ acceleratedOrbit 15 27637 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27637) = 3 ^ 8 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27637.1, data_15_27637.2]

/-- Complete interval computation for depth 15, residue 27638. -/
theorem bounds_15_27638 : exactInterval 15 27638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27638 : oddCount 27638 15 = 10 ∧ acceleratedOrbit 15 27638 = 49814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27638) = 3 ^ 10 * m + 49814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27638.1, data_15_27638.2]

/-- Complete interval computation for depth 15, residue 27639. -/
theorem bounds_15_27639 : exactInterval 15 27639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27639 : oddCount 27639 15 = 10 ∧ acceleratedOrbit 15 27639 = 49814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27639) = 3 ^ 10 * m + 49814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27639.1, data_15_27639.2]

/-- Complete interval computation for depth 15, residue 27640. -/
theorem bounds_15_27640 : exactInterval 15 27640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27640 : oddCount 27640 15 = 8 ∧ acceleratedOrbit 15 27640 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27640) = 3 ^ 8 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27640.1, data_15_27640.2]

/-- Complete interval computation for depth 15, residue 27641. -/
theorem bounds_15_27641 : exactInterval 15 27641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27641 : oddCount 27641 15 = 12 ∧ acceleratedOrbit 15 27641 = 448334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27641) = 3 ^ 12 * m + 448334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27641.1, data_15_27641.2]

/-- Complete interval computation for depth 15, residue 27642. -/
theorem bounds_15_27642 : exactInterval 15 27642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27642 : oddCount 27642 15 = 8 ∧ acceleratedOrbit 15 27642 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27642) = 3 ^ 8 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27642.1, data_15_27642.2]

/-- Complete interval computation for depth 15, residue 27643. -/
theorem bounds_15_27643 : exactInterval 15 27643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27643 : oddCount 27643 15 = 9 ∧ acceleratedOrbit 15 27643 = 16606 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27643) = 3 ^ 9 * m + 16606 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27643.1, data_15_27643.2]

/-- Complete interval computation for depth 15, residue 27644. -/
theorem bounds_15_27644 : exactInterval 15 27644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27644 : oddCount 27644 15 = 10 ∧ acceleratedOrbit 15 27644 = 49823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27644) = 3 ^ 10 * m + 49823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27644.1, data_15_27644.2]

/-- Complete interval computation for depth 15, residue 27645. -/
theorem bounds_15_27645 : exactInterval 15 27645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27645 : oddCount 27645 15 = 10 ∧ acceleratedOrbit 15 27645 = 49823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27645) = 3 ^ 10 * m + 49823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27645.1, data_15_27645.2]

/-- Complete interval computation for depth 15, residue 27646. -/
theorem bounds_15_27646 : exactInterval 15 27646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27646 : oddCount 27646 15 = 10 ∧ acceleratedOrbit 15 27646 = 49823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27646) = 3 ^ 10 * m + 49823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27646.1, data_15_27646.2]

/-- Complete interval computation for depth 15, residue 27647. -/
theorem bounds_15_27647 : exactInterval 15 27647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27647 : oddCount 27647 15 = 13 ∧ acceleratedOrbit 15 27647 = 1345211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27647) = 3 ^ 13 * m + 1345211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27647.1, data_15_27647.2]

/-- Complete interval computation for depth 15, residue 27648. -/
theorem bounds_15_27648 : exactInterval 15 27648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27648 : oddCount 27648 15 = 4 ∧ acceleratedOrbit 15 27648 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27648) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27648.1, data_15_27648.2]

/-- Complete interval computation for depth 15, residue 27649. -/
theorem bounds_15_27649 : exactInterval 15 27649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27649 : oddCount 27649 15 = 7 ∧ acceleratedOrbit 15 27649 = 1846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27649) = 3 ^ 7 * m + 1846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27649.1, data_15_27649.2]

/-- Complete interval computation for depth 15, residue 27650. -/
theorem bounds_15_27650 : exactInterval 15 27650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27650 : oddCount 27650 15 = 7 ∧ acceleratedOrbit 15 27650 = 1846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27650) = 3 ^ 7 * m + 1846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27650.1, data_15_27650.2]

/-- Complete interval computation for depth 15, residue 27651. -/
theorem bounds_15_27651 : exactInterval 15 27651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27651 : oddCount 27651 15 = 7 ∧ acceleratedOrbit 15 27651 = 1846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27651) = 3 ^ 7 * m + 1846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27651.1, data_15_27651.2]

/-- Complete interval computation for depth 15, residue 27652. -/
theorem bounds_15_27652 : exactInterval 15 27652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27652 : oddCount 27652 15 = 6 ∧ acceleratedOrbit 15 27652 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27652) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27652.1, data_15_27652.2]

/-- Complete interval computation for depth 15, residue 27653. -/
theorem bounds_15_27653 : exactInterval 15 27653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27653 : oddCount 27653 15 = 6 ∧ acceleratedOrbit 15 27653 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27653) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27653.1, data_15_27653.2]

/-- Complete interval computation for depth 15, residue 27654. -/
theorem bounds_15_27654 : exactInterval 15 27654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27654 : oddCount 27654 15 = 6 ∧ acceleratedOrbit 15 27654 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27654) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27654.1, data_15_27654.2]

/-- Complete interval computation for depth 15, residue 27655. -/
theorem bounds_15_27655 : exactInterval 15 27655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27655 : oddCount 27655 15 = 7 ∧ acceleratedOrbit 15 27655 = 1846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27655) = 3 ^ 7 * m + 1846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27655.1, data_15_27655.2]

end Collatz.Research.PassageAtlas.Batch0844
