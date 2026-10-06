import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0020

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 622. -/
theorem bounds_15_622 : exactInterval 15 622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_622 : oddCount 622 15 = 9 ∧ acceleratedOrbit 15 622 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 622) = 3 ^ 9 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_622.1, data_15_622.2]

/-- Complete interval computation for depth 15, residue 623. -/
theorem bounds_15_623 : exactInterval 15 623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_623 : oddCount 623 15 = 8 ∧ acceleratedOrbit 15 623 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 623) = 3 ^ 8 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_623.1, data_15_623.2]

/-- Complete interval computation for depth 15, residue 624. -/
theorem bounds_15_624 : exactInterval 15 624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_624 : oddCount 624 15 = 7 ∧ acceleratedOrbit 15 624 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 624) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_624.1, data_15_624.2]

/-- Complete interval computation for depth 15, residue 625. -/
theorem bounds_15_625 : exactInterval 15 625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_625 : oddCount 625 15 = 5 ∧ acceleratedOrbit 15 625 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 625) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_625.1, data_15_625.2]

/-- Complete interval computation for depth 15, residue 626. -/
theorem bounds_15_626 : exactInterval 15 626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_626 : oddCount 626 15 = 9 ∧ acceleratedOrbit 15 626 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 626) = 3 ^ 9 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_626.1, data_15_626.2]

/-- Complete interval computation for depth 15, residue 627. -/
theorem bounds_15_627 : exactInterval 15 627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_627 : oddCount 627 15 = 9 ∧ acceleratedOrbit 15 627 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 627) = 3 ^ 9 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_627.1, data_15_627.2]

/-- Complete interval computation for depth 15, residue 628. -/
theorem bounds_15_628 : exactInterval 15 628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_628 : oddCount 628 15 = 7 ∧ acceleratedOrbit 15 628 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 628) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_628.1, data_15_628.2]

/-- Complete interval computation for depth 15, residue 629. -/
theorem bounds_15_629 : exactInterval 15 629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_629 : oddCount 629 15 = 7 ∧ acceleratedOrbit 15 629 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 629) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_629.1, data_15_629.2]

/-- Complete interval computation for depth 15, residue 630. -/
theorem bounds_15_630 : exactInterval 15 630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_630 : oddCount 630 15 = 7 ∧ acceleratedOrbit 15 630 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 630) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_630.1, data_15_630.2]

/-- Complete interval computation for depth 15, residue 631. -/
theorem bounds_15_631 : exactInterval 15 631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_631 : oddCount 631 15 = 7 ∧ acceleratedOrbit 15 631 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 631) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_631.1, data_15_631.2]

/-- Complete interval computation for depth 15, residue 632. -/
theorem bounds_15_632 : exactInterval 15 632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_632 : oddCount 632 15 = 7 ∧ acceleratedOrbit 15 632 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 632) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_632.1, data_15_632.2]

/-- Complete interval computation for depth 15, residue 633. -/
theorem bounds_15_633 : exactInterval 15 633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_633 : oddCount 633 15 = 8 ∧ acceleratedOrbit 15 633 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 633) = 3 ^ 8 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_633.1, data_15_633.2]

/-- Complete interval computation for depth 15, residue 634. -/
theorem bounds_15_634 : exactInterval 15 634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_634 : oddCount 634 15 = 7 ∧ acceleratedOrbit 15 634 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 634) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_634.1, data_15_634.2]

/-- Complete interval computation for depth 15, residue 635. -/
theorem bounds_15_635 : exactInterval 15 635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_635 : oddCount 635 15 = 8 ∧ acceleratedOrbit 15 635 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 635) = 3 ^ 8 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_635.1, data_15_635.2]

/-- Complete interval computation for depth 15, residue 636. -/
theorem bounds_15_636 : exactInterval 15 636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_636 : oddCount 636 15 = 10 ∧ acceleratedOrbit 15 636 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 636) = 3 ^ 10 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_636.1, data_15_636.2]

/-- Complete interval computation for depth 15, residue 637. -/
theorem bounds_15_637 : exactInterval 15 637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_637 : oddCount 637 15 = 10 ∧ acceleratedOrbit 15 637 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 637) = 3 ^ 10 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_637.1, data_15_637.2]

/-- Complete interval computation for depth 15, residue 638. -/
theorem bounds_15_638 : exactInterval 15 638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_638 : oddCount 638 15 = 10 ∧ acceleratedOrbit 15 638 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 638) = 3 ^ 10 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_638.1, data_15_638.2]

/-- Complete interval computation for depth 15, residue 639. -/
theorem bounds_15_639 : exactInterval 15 639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_639 : oddCount 639 15 = 12 ∧ acceleratedOrbit 15 639 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 639) = 3 ^ 12 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_639.1, data_15_639.2]

/-- Complete interval computation for depth 15, residue 640. -/
theorem bounds_15_640 : exactInterval 15 640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_640 : oddCount 640 15 = 3 ∧ acceleratedOrbit 15 640 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 640) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_640.1, data_15_640.2]

/-- Complete interval computation for depth 15, residue 641. -/
theorem bounds_15_641 : exactInterval 15 641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_641 : oddCount 641 15 = 7 ∧ acceleratedOrbit 15 641 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 641) = 3 ^ 7 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_641.1, data_15_641.2]

/-- Complete interval computation for depth 15, residue 642. -/
theorem bounds_15_642 : exactInterval 15 642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_642 : oddCount 642 15 = 5 ∧ acceleratedOrbit 15 642 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 642) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_642.1, data_15_642.2]

/-- Complete interval computation for depth 15, residue 643. -/
theorem bounds_15_643 : exactInterval 15 643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_643 : oddCount 643 15 = 5 ∧ acceleratedOrbit 15 643 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 643) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_643.1, data_15_643.2]

/-- Complete interval computation for depth 15, residue 644. -/
theorem bounds_15_644 : exactInterval 15 644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_644 : oddCount 644 15 = 9 ∧ acceleratedOrbit 15 644 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 644) = 3 ^ 9 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_644.1, data_15_644.2]

/-- Complete interval computation for depth 15, residue 645. -/
theorem bounds_15_645 : exactInterval 15 645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_645 : oddCount 645 15 = 9 ∧ acceleratedOrbit 15 645 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 645) = 3 ^ 9 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_645.1, data_15_645.2]

/-- Complete interval computation for depth 15, residue 646. -/
theorem bounds_15_646 : exactInterval 15 646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_646 : oddCount 646 15 = 9 ∧ acceleratedOrbit 15 646 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 646) = 3 ^ 9 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_646.1, data_15_646.2]

/-- Complete interval computation for depth 15, residue 647. -/
theorem bounds_15_647 : exactInterval 15 647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_647 : oddCount 647 15 = 7 ∧ acceleratedOrbit 15 647 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 647) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_647.1, data_15_647.2]

/-- Complete interval computation for depth 15, residue 648. -/
theorem bounds_15_648 : exactInterval 15 648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_648 : oddCount 648 15 = 5 ∧ acceleratedOrbit 15 648 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 648) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_648.1, data_15_648.2]

/-- Complete interval computation for depth 15, residue 649. -/
theorem bounds_15_649 : exactInterval 15 649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_649 : oddCount 649 15 = 10 ∧ acceleratedOrbit 15 649 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 649) = 3 ^ 10 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_649.1, data_15_649.2]

/-- Complete interval computation for depth 15, residue 650. -/
theorem bounds_15_650 : exactInterval 15 650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_650 : oddCount 650 15 = 5 ∧ acceleratedOrbit 15 650 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 650) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_650.1, data_15_650.2]

/-- Complete interval computation for depth 15, residue 651. -/
theorem bounds_15_651 : exactInterval 15 651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_651 : oddCount 651 15 = 9 ∧ acceleratedOrbit 15 651 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 651) = 3 ^ 9 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_651.1, data_15_651.2]

/-- Complete interval computation for depth 15, residue 652. -/
theorem bounds_15_652 : exactInterval 15 652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_652 : oddCount 652 15 = 5 ∧ acceleratedOrbit 15 652 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 652) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_652.1, data_15_652.2]

/-- Complete interval computation for depth 15, residue 653. -/
theorem bounds_15_653 : exactInterval 15 653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_653 : oddCount 653 15 = 5 ∧ acceleratedOrbit 15 653 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 653) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_653.1, data_15_653.2]

/-- Complete interval computation for depth 15, residue 654. -/
theorem bounds_15_654 : exactInterval 15 654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_654 : oddCount 654 15 = 11 ∧ acceleratedOrbit 15 654 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 654) = 3 ^ 11 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_654.1, data_15_654.2]

end Collatz.Research.PassageAtlas.Batch0020
