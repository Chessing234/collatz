import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0966

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31621. -/
theorem bounds_15_31621 : exactInterval 15 31621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31621 : oddCount 31621 15 = 7 ∧ acceleratedOrbit 15 31621 = 2111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31621) = 3 ^ 7 * m + 2111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31621.1, data_15_31621.2]

/-- Complete interval computation for depth 15, residue 31622. -/
theorem bounds_15_31622 : exactInterval 15 31622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31622 : oddCount 31622 15 = 7 ∧ acceleratedOrbit 15 31622 = 2111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31622) = 3 ^ 7 * m + 2111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31622.1, data_15_31622.2]

/-- Complete interval computation for depth 15, residue 31623. -/
theorem bounds_15_31623 : exactInterval 15 31623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31623 : oddCount 31623 15 = 7 ∧ acceleratedOrbit 15 31623 = 2111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31623) = 3 ^ 7 * m + 2111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31623.1, data_15_31623.2]

/-- Complete interval computation for depth 15, residue 31624. -/
theorem bounds_15_31624 : exactInterval 15 31624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31624 : oddCount 31624 15 = 5 ∧ acceleratedOrbit 15 31624 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31624) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31624.1, data_15_31624.2]

/-- Complete interval computation for depth 15, residue 31625. -/
theorem bounds_15_31625 : exactInterval 15 31625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31625 : oddCount 31625 15 = 11 ∧ acceleratedOrbit 15 31625 = 170981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31625) = 3 ^ 11 * m + 170981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31625.1, data_15_31625.2]

/-- Complete interval computation for depth 15, residue 31626. -/
theorem bounds_15_31626 : exactInterval 15 31626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31626 : oddCount 31626 15 = 5 ∧ acceleratedOrbit 15 31626 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31626) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31626.1, data_15_31626.2]

/-- Complete interval computation for depth 15, residue 31627. -/
theorem bounds_15_31627 : exactInterval 15 31627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31627 : oddCount 31627 15 = 10 ∧ acceleratedOrbit 15 31627 = 56999 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31627) = 3 ^ 10 * m + 56999 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31627.1, data_15_31627.2]

/-- Complete interval computation for depth 15, residue 31628. -/
theorem bounds_15_31628 : exactInterval 15 31628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31628 : oddCount 31628 15 = 5 ∧ acceleratedOrbit 15 31628 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31628) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31628.1, data_15_31628.2]

/-- Complete interval computation for depth 15, residue 31629. -/
theorem bounds_15_31629 : exactInterval 15 31629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31629 : oddCount 31629 15 = 5 ∧ acceleratedOrbit 15 31629 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31629) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31629.1, data_15_31629.2]

/-- Complete interval computation for depth 15, residue 31630. -/
theorem bounds_15_31630 : exactInterval 15 31630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31630 : oddCount 31630 15 = 8 ∧ acceleratedOrbit 15 31630 = 6335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31630) = 3 ^ 8 * m + 6335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31630.1, data_15_31630.2]

/-- Complete interval computation for depth 15, residue 31631. -/
theorem bounds_15_31631 : exactInterval 15 31631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31631 : oddCount 31631 15 = 8 ∧ acceleratedOrbit 15 31631 = 6335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31631) = 3 ^ 8 * m + 6335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31631.1, data_15_31631.2]

/-- Complete interval computation for depth 15, residue 31632. -/
theorem bounds_15_31632 : exactInterval 15 31632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31632 : oddCount 31632 15 = 5 ∧ acceleratedOrbit 15 31632 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31632) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31632.1, data_15_31632.2]

/-- Complete interval computation for depth 15, residue 31633. -/
theorem bounds_15_31633 : exactInterval 15 31633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31633 : oddCount 31633 15 = 6 ∧ acceleratedOrbit 15 31633 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31633) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31633.1, data_15_31633.2]

/-- Complete interval computation for depth 15, residue 31634. -/
theorem bounds_15_31634 : exactInterval 15 31634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31634 : oddCount 31634 15 = 6 ∧ acceleratedOrbit 15 31634 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31634) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31634.1, data_15_31634.2]

/-- Complete interval computation for depth 15, residue 31635. -/
theorem bounds_15_31635 : exactInterval 15 31635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31635 : oddCount 31635 15 = 6 ∧ acceleratedOrbit 15 31635 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31635) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31635.1, data_15_31635.2]

/-- Complete interval computation for depth 15, residue 31636. -/
theorem bounds_15_31636 : exactInterval 15 31636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31636 : oddCount 31636 15 = 5 ∧ acceleratedOrbit 15 31636 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31636) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31636.1, data_15_31636.2]

/-- Complete interval computation for depth 15, residue 31637. -/
theorem bounds_15_31637 : exactInterval 15 31637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31637 : oddCount 31637 15 = 5 ∧ acceleratedOrbit 15 31637 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31637) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31637.1, data_15_31637.2]

/-- Complete interval computation for depth 15, residue 31638. -/
theorem bounds_15_31638 : exactInterval 15 31638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31638 : oddCount 31638 15 = 8 ∧ acceleratedOrbit 15 31638 = 6338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31638) = 3 ^ 8 * m + 6338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31638.1, data_15_31638.2]

/-- Complete interval computation for depth 15, residue 31639. -/
theorem bounds_15_31639 : exactInterval 15 31639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31639 : oddCount 31639 15 = 8 ∧ acceleratedOrbit 15 31639 = 6338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31639) = 3 ^ 8 * m + 6338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31639.1, data_15_31639.2]

/-- Complete interval computation for depth 15, residue 31640. -/
theorem bounds_15_31640 : exactInterval 15 31640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31640 : oddCount 31640 15 = 5 ∧ acceleratedOrbit 15 31640 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31640) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31640.1, data_15_31640.2]

/-- Complete interval computation for depth 15, residue 31641. -/
theorem bounds_15_31641 : exactInterval 15 31641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31641 : oddCount 31641 15 = 8 ∧ acceleratedOrbit 15 31641 = 6338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31641) = 3 ^ 8 * m + 6338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31641.1, data_15_31641.2]

/-- Complete interval computation for depth 15, residue 31642. -/
theorem bounds_15_31642 : exactInterval 15 31642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31642 : oddCount 31642 15 = 5 ∧ acceleratedOrbit 15 31642 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31642) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31642.1, data_15_31642.2]

/-- Complete interval computation for depth 15, residue 31643. -/
theorem bounds_15_31643 : exactInterval 15 31643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31643 : oddCount 31643 15 = 6 ∧ acceleratedOrbit 15 31643 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31643) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31643.1, data_15_31643.2]

/-- Complete interval computation for depth 15, residue 31644. -/
theorem bounds_15_31644 : exactInterval 15 31644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31644 : oddCount 31644 15 = 8 ∧ acceleratedOrbit 15 31644 = 6337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31644) = 3 ^ 8 * m + 6337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31644.1, data_15_31644.2]

/-- Complete interval computation for depth 15, residue 31645. -/
theorem bounds_15_31645 : exactInterval 15 31645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31645 : oddCount 31645 15 = 8 ∧ acceleratedOrbit 15 31645 = 6337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31645) = 3 ^ 8 * m + 6337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31645.1, data_15_31645.2]

/-- Complete interval computation for depth 15, residue 31646. -/
theorem bounds_15_31646 : exactInterval 15 31646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31646 : oddCount 31646 15 = 8 ∧ acceleratedOrbit 15 31646 = 6337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31646) = 3 ^ 8 * m + 6337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31646.1, data_15_31646.2]

/-- Complete interval computation for depth 15, residue 31647. -/
theorem bounds_15_31647 : exactInterval 15 31647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31647 : oddCount 31647 15 = 8 ∧ acceleratedOrbit 15 31647 = 6337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31647) = 3 ^ 8 * m + 6337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31647.1, data_15_31647.2]

/-- Complete interval computation for depth 15, residue 31648. -/
theorem bounds_15_31648 : exactInterval 15 31648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31648 : oddCount 31648 15 = 5 ∧ acceleratedOrbit 15 31648 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31648) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31648.1, data_15_31648.2]

/-- Complete interval computation for depth 15, residue 31649. -/
theorem bounds_15_31649 : exactInterval 15 31649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31649 : oddCount 31649 15 = 8 ∧ acceleratedOrbit 15 31649 = 6338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31649) = 3 ^ 8 * m + 6338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31649.1, data_15_31649.2]

/-- Complete interval computation for depth 15, residue 31650. -/
theorem bounds_15_31650 : exactInterval 15 31650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31650 : oddCount 31650 15 = 5 ∧ acceleratedOrbit 15 31650 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31650) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31650.1, data_15_31650.2]

/-- Complete interval computation for depth 15, residue 31651. -/
theorem bounds_15_31651 : exactInterval 15 31651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31651 : oddCount 31651 15 = 5 ∧ acceleratedOrbit 15 31651 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31651) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31651.1, data_15_31651.2]

/-- Complete interval computation for depth 15, residue 31652. -/
theorem bounds_15_31652 : exactInterval 15 31652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31652 : oddCount 31652 15 = 7 ∧ acceleratedOrbit 15 31652 = 2113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31652) = 3 ^ 7 * m + 2113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31652.1, data_15_31652.2]

end Collatz.Research.PassageAtlas.Batch0966
