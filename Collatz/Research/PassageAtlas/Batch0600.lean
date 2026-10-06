import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0600

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19628. -/
theorem bounds_15_19628 : exactInterval 15 19628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19628 : oddCount 19628 15 = 6 ∧ acceleratedOrbit 15 19628 = 437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19628) = 3 ^ 6 * m + 437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19628.1, data_15_19628.2]

/-- Complete interval computation for depth 15, residue 19629. -/
theorem bounds_15_19629 : exactInterval 15 19629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19629 : oddCount 19629 15 = 6 ∧ acceleratedOrbit 15 19629 = 437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19629) = 3 ^ 6 * m + 437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19629.1, data_15_19629.2]

/-- Complete interval computation for depth 15, residue 19630. -/
theorem bounds_15_19630 : exactInterval 15 19630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19630 : oddCount 19630 15 = 6 ∧ acceleratedOrbit 15 19630 = 437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19630) = 3 ^ 6 * m + 437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19630.1, data_15_19630.2]

/-- Complete interval computation for depth 15, residue 19631. -/
theorem bounds_15_19631 : exactInterval 15 19631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19631 : oddCount 19631 15 = 8 ∧ acceleratedOrbit 15 19631 = 3931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19631) = 3 ^ 8 * m + 3931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19631.1, data_15_19631.2]

/-- Complete interval computation for depth 15, residue 19632. -/
theorem bounds_15_19632 : exactInterval 15 19632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19632 : oddCount 19632 15 = 5 ∧ acceleratedOrbit 15 19632 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19632) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19632.1, data_15_19632.2]

/-- Complete interval computation for depth 15, residue 19633. -/
theorem bounds_15_19633 : exactInterval 15 19633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19633 : oddCount 19633 15 = 6 ∧ acceleratedOrbit 15 19633 = 437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19633) = 3 ^ 6 * m + 437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19633.1, data_15_19633.2]

/-- Complete interval computation for depth 15, residue 19634. -/
theorem bounds_15_19634 : exactInterval 15 19634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19634 : oddCount 19634 15 = 6 ∧ acceleratedOrbit 15 19634 = 437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19634) = 3 ^ 6 * m + 437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19634.1, data_15_19634.2]

/-- Complete interval computation for depth 15, residue 19635. -/
theorem bounds_15_19635 : exactInterval 15 19635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19635 : oddCount 19635 15 = 6 ∧ acceleratedOrbit 15 19635 = 437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19635) = 3 ^ 6 * m + 437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19635.1, data_15_19635.2]

/-- Complete interval computation for depth 15, residue 19636. -/
theorem bounds_15_19636 : exactInterval 15 19636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19636 : oddCount 19636 15 = 5 ∧ acceleratedOrbit 15 19636 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19636) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19636.1, data_15_19636.2]

/-- Complete interval computation for depth 15, residue 19637. -/
theorem bounds_15_19637 : exactInterval 15 19637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19637 : oddCount 19637 15 = 5 ∧ acceleratedOrbit 15 19637 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19637) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19637.1, data_15_19637.2]

/-- Complete interval computation for depth 15, residue 19638. -/
theorem bounds_15_19638 : exactInterval 15 19638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19638 : oddCount 19638 15 = 10 ∧ acceleratedOrbit 15 19638 = 35396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19638) = 3 ^ 10 * m + 35396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19638.1, data_15_19638.2]

/-- Complete interval computation for depth 15, residue 19639. -/
theorem bounds_15_19639 : exactInterval 15 19639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19639 : oddCount 19639 15 = 10 ∧ acceleratedOrbit 15 19639 = 35396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19639) = 3 ^ 10 * m + 35396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19639.1, data_15_19639.2]

/-- Complete interval computation for depth 15, residue 19640. -/
theorem bounds_15_19640 : exactInterval 15 19640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19640 : oddCount 19640 15 = 5 ∧ acceleratedOrbit 15 19640 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19640) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19640.1, data_15_19640.2]

/-- Complete interval computation for depth 15, residue 19641. -/
theorem bounds_15_19641 : exactInterval 15 19641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19641 : oddCount 19641 15 = 9 ∧ acceleratedOrbit 15 19641 = 11801 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19641) = 3 ^ 9 * m + 11801 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19641.1, data_15_19641.2]

/-- Complete interval computation for depth 15, residue 19642. -/
theorem bounds_15_19642 : exactInterval 15 19642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19642 : oddCount 19642 15 = 5 ∧ acceleratedOrbit 15 19642 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19642) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19642.1, data_15_19642.2]

/-- Complete interval computation for depth 15, residue 19643. -/
theorem bounds_15_19643 : exactInterval 15 19643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19643 : oddCount 19643 15 = 9 ∧ acceleratedOrbit 15 19643 = 11801 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19643) = 3 ^ 9 * m + 11801 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19643.1, data_15_19643.2]

/-- Complete interval computation for depth 15, residue 19644. -/
theorem bounds_15_19644 : exactInterval 15 19644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19644 : oddCount 19644 15 = 8 ∧ acceleratedOrbit 15 19644 = 3935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19644) = 3 ^ 8 * m + 3935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19644.1, data_15_19644.2]

/-- Complete interval computation for depth 15, residue 19645. -/
theorem bounds_15_19645 : exactInterval 15 19645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19645 : oddCount 19645 15 = 8 ∧ acceleratedOrbit 15 19645 = 3935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19645) = 3 ^ 8 * m + 3935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19645.1, data_15_19645.2]

/-- Complete interval computation for depth 15, residue 19646. -/
theorem bounds_15_19646 : exactInterval 15 19646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19646 : oddCount 19646 15 = 8 ∧ acceleratedOrbit 15 19646 = 3935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19646) = 3 ^ 8 * m + 3935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19646.1, data_15_19646.2]

/-- Complete interval computation for depth 15, residue 19647. -/
theorem bounds_15_19647 : exactInterval 15 19647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19647 : oddCount 19647 15 = 10 ∧ acceleratedOrbit 15 19647 = 35407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19647) = 3 ^ 10 * m + 35407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19647.1, data_15_19647.2]

/-- Complete interval computation for depth 15, residue 19648. -/
theorem bounds_15_19648 : exactInterval 15 19648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19648 : oddCount 19648 15 = 4 ∧ acceleratedOrbit 15 19648 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19648) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19648.1, data_15_19648.2]

/-- Complete interval computation for depth 15, residue 19649. -/
theorem bounds_15_19649 : exactInterval 15 19649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19649 : oddCount 19649 15 = 7 ∧ acceleratedOrbit 15 19649 = 1313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19649) = 3 ^ 7 * m + 1313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19649.1, data_15_19649.2]

/-- Complete interval computation for depth 15, residue 19650. -/
theorem bounds_15_19650 : exactInterval 15 19650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19650 : oddCount 19650 15 = 7 ∧ acceleratedOrbit 15 19650 = 1313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19650) = 3 ^ 7 * m + 1313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19650.1, data_15_19650.2]

/-- Complete interval computation for depth 15, residue 19651. -/
theorem bounds_15_19651 : exactInterval 15 19651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19651 : oddCount 19651 15 = 7 ∧ acceleratedOrbit 15 19651 = 1313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19651) = 3 ^ 7 * m + 1313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19651.1, data_15_19651.2]

/-- Complete interval computation for depth 15, residue 19652. -/
theorem bounds_15_19652 : exactInterval 15 19652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19652 : oddCount 19652 15 = 5 ∧ acceleratedOrbit 15 19652 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19652) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19652.1, data_15_19652.2]

/-- Complete interval computation for depth 15, residue 19653. -/
theorem bounds_15_19653 : exactInterval 15 19653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19653 : oddCount 19653 15 = 5 ∧ acceleratedOrbit 15 19653 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19653) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19653.1, data_15_19653.2]

/-- Complete interval computation for depth 15, residue 19654. -/
theorem bounds_15_19654 : exactInterval 15 19654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19654 : oddCount 19654 15 = 5 ∧ acceleratedOrbit 15 19654 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19654) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19654.1, data_15_19654.2]

/-- Complete interval computation for depth 15, residue 19655. -/
theorem bounds_15_19655 : exactInterval 15 19655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19655 : oddCount 19655 15 = 7 ∧ acceleratedOrbit 15 19655 = 1312 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19655) = 3 ^ 7 * m + 1312 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19655.1, data_15_19655.2]

/-- Complete interval computation for depth 15, residue 19656. -/
theorem bounds_15_19656 : exactInterval 15 19656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19656 : oddCount 19656 15 = 5 ∧ acceleratedOrbit 15 19656 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19656) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19656.1, data_15_19656.2]

/-- Complete interval computation for depth 15, residue 19657. -/
theorem bounds_15_19657 : exactInterval 15 19657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19657 : oddCount 19657 15 = 7 ∧ acceleratedOrbit 15 19657 = 1313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19657) = 3 ^ 7 * m + 1313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19657.1, data_15_19657.2]

/-- Complete interval computation for depth 15, residue 19658. -/
theorem bounds_15_19658 : exactInterval 15 19658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19658 : oddCount 19658 15 = 5 ∧ acceleratedOrbit 15 19658 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19658) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19658.1, data_15_19658.2]

/-- Complete interval computation for depth 15, residue 19659. -/
theorem bounds_15_19659 : exactInterval 15 19659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19659 : oddCount 19659 15 = 7 ∧ acceleratedOrbit 15 19659 = 1313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19659) = 3 ^ 7 * m + 1313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19659.1, data_15_19659.2]

end Collatz.Research.PassageAtlas.Batch0600
