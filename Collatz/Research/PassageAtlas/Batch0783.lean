import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0783

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25624. -/
theorem bounds_15_25624 : exactInterval 15 25624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25624 : oddCount 25624 15 = 5 ∧ acceleratedOrbit 15 25624 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25624) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25624.1, data_15_25624.2]

/-- Complete interval computation for depth 15, residue 25625. -/
theorem bounds_15_25625 : exactInterval 15 25625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25625 : oddCount 25625 15 = 8 ∧ acceleratedOrbit 15 25625 = 5132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25625) = 3 ^ 8 * m + 5132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25625.1, data_15_25625.2]

/-- Complete interval computation for depth 15, residue 25626. -/
theorem bounds_15_25626 : exactInterval 15 25626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25626 : oddCount 25626 15 = 5 ∧ acceleratedOrbit 15 25626 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25626) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25626.1, data_15_25626.2]

/-- Complete interval computation for depth 15, residue 25627. -/
theorem bounds_15_25627 : exactInterval 15 25627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25627 : oddCount 25627 15 = 12 ∧ acceleratedOrbit 15 25627 = 415651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25627) = 3 ^ 12 * m + 415651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25627.1, data_15_25627.2]

/-- Complete interval computation for depth 15, residue 25628. -/
theorem bounds_15_25628 : exactInterval 15 25628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25628 : oddCount 25628 15 = 7 ∧ acceleratedOrbit 15 25628 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25628) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25628.1, data_15_25628.2]

/-- Complete interval computation for depth 15, residue 25629. -/
theorem bounds_15_25629 : exactInterval 15 25629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25629 : oddCount 25629 15 = 7 ∧ acceleratedOrbit 15 25629 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25629) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25629.1, data_15_25629.2]

/-- Complete interval computation for depth 15, residue 25630. -/
theorem bounds_15_25630 : exactInterval 15 25630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25630 : oddCount 25630 15 = 7 ∧ acceleratedOrbit 15 25630 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25630) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25630.1, data_15_25630.2]

/-- Complete interval computation for depth 15, residue 25631. -/
theorem bounds_15_25631 : exactInterval 15 25631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25631 : oddCount 25631 15 = 12 ∧ acceleratedOrbit 15 25631 = 415712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25631) = 3 ^ 12 * m + 415712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25631.1, data_15_25631.2]

/-- Complete interval computation for depth 15, residue 25632. -/
theorem bounds_15_25632 : exactInterval 15 25632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25632 : oddCount 25632 15 = 5 ∧ acceleratedOrbit 15 25632 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25632) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25632.1, data_15_25632.2]

/-- Complete interval computation for depth 15, residue 25633. -/
theorem bounds_15_25633 : exactInterval 15 25633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25633 : oddCount 25633 15 = 9 ∧ acceleratedOrbit 15 25633 = 15400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25633) = 3 ^ 9 * m + 15400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25633.1, data_15_25633.2]

/-- Complete interval computation for depth 15, residue 25634. -/
theorem bounds_15_25634 : exactInterval 15 25634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25634 : oddCount 25634 15 = 5 ∧ acceleratedOrbit 15 25634 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25634) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25634.1, data_15_25634.2]

/-- Complete interval computation for depth 15, residue 25635. -/
theorem bounds_15_25635 : exactInterval 15 25635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25635 : oddCount 25635 15 = 5 ∧ acceleratedOrbit 15 25635 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25635) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25635.1, data_15_25635.2]

/-- Complete interval computation for depth 15, residue 25636. -/
theorem bounds_15_25636 : exactInterval 15 25636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25636 : oddCount 25636 15 = 7 ∧ acceleratedOrbit 15 25636 = 1712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25636) = 3 ^ 7 * m + 1712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25636.1, data_15_25636.2]

/-- Complete interval computation for depth 15, residue 25637. -/
theorem bounds_15_25637 : exactInterval 15 25637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25637 : oddCount 25637 15 = 7 ∧ acceleratedOrbit 15 25637 = 1712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25637) = 3 ^ 7 * m + 1712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25637.1, data_15_25637.2]

/-- Complete interval computation for depth 15, residue 25638. -/
theorem bounds_15_25638 : exactInterval 15 25638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25638 : oddCount 25638 15 = 7 ∧ acceleratedOrbit 15 25638 = 1712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25638) = 3 ^ 7 * m + 1712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25638.1, data_15_25638.2]

/-- Complete interval computation for depth 15, residue 25639. -/
theorem bounds_15_25639 : exactInterval 15 25639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25639 : oddCount 25639 15 = 9 ∧ acceleratedOrbit 15 25639 = 15403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25639) = 3 ^ 9 * m + 15403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25639.1, data_15_25639.2]

/-- Complete interval computation for depth 15, residue 25640. -/
theorem bounds_15_25640 : exactInterval 15 25640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25640 : oddCount 25640 15 = 5 ∧ acceleratedOrbit 15 25640 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25640) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25640.1, data_15_25640.2]

/-- Complete interval computation for depth 15, residue 25641. -/
theorem bounds_15_25641 : exactInterval 15 25641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25641 : oddCount 25641 15 = 10 ∧ acceleratedOrbit 15 25641 = 46210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25641) = 3 ^ 10 * m + 46210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25641.1, data_15_25641.2]

/-- Complete interval computation for depth 15, residue 25642. -/
theorem bounds_15_25642 : exactInterval 15 25642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25642 : oddCount 25642 15 = 5 ∧ acceleratedOrbit 15 25642 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25642) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25642.1, data_15_25642.2]

/-- Complete interval computation for depth 15, residue 25643. -/
theorem bounds_15_25643 : exactInterval 15 25643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25643 : oddCount 25643 15 = 7 ∧ acceleratedOrbit 15 25643 = 1712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25643) = 3 ^ 7 * m + 1712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25643.1, data_15_25643.2]

/-- Complete interval computation for depth 15, residue 25644. -/
theorem bounds_15_25644 : exactInterval 15 25644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25644 : oddCount 25644 15 = 6 ∧ acceleratedOrbit 15 25644 = 571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25644) = 3 ^ 6 * m + 571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25644.1, data_15_25644.2]

/-- Complete interval computation for depth 15, residue 25645. -/
theorem bounds_15_25645 : exactInterval 15 25645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25645 : oddCount 25645 15 = 6 ∧ acceleratedOrbit 15 25645 = 571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25645) = 3 ^ 6 * m + 571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25645.1, data_15_25645.2]

/-- Complete interval computation for depth 15, residue 25646. -/
theorem bounds_15_25646 : exactInterval 15 25646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25646 : oddCount 25646 15 = 6 ∧ acceleratedOrbit 15 25646 = 571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25646) = 3 ^ 6 * m + 571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25646.1, data_15_25646.2]

/-- Complete interval computation for depth 15, residue 25647. -/
theorem bounds_15_25647 : exactInterval 15 25647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25647 : oddCount 25647 15 = 9 ∧ acceleratedOrbit 15 25647 = 15407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25647) = 3 ^ 9 * m + 15407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25647.1, data_15_25647.2]

/-- Complete interval computation for depth 15, residue 25648. -/
theorem bounds_15_25648 : exactInterval 15 25648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25648 : oddCount 25648 15 = 5 ∧ acceleratedOrbit 15 25648 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25648) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25648.1, data_15_25648.2]

/-- Complete interval computation for depth 15, residue 25649. -/
theorem bounds_15_25649 : exactInterval 15 25649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25649 : oddCount 25649 15 = 6 ∧ acceleratedOrbit 15 25649 = 571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25649) = 3 ^ 6 * m + 571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25649.1, data_15_25649.2]

/-- Complete interval computation for depth 15, residue 25650. -/
theorem bounds_15_25650 : exactInterval 15 25650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25650 : oddCount 25650 15 = 6 ∧ acceleratedOrbit 15 25650 = 571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25650) = 3 ^ 6 * m + 571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25650.1, data_15_25650.2]

/-- Complete interval computation for depth 15, residue 25651. -/
theorem bounds_15_25651 : exactInterval 15 25651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25651 : oddCount 25651 15 = 6 ∧ acceleratedOrbit 15 25651 = 571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25651) = 3 ^ 6 * m + 571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25651.1, data_15_25651.2]

/-- Complete interval computation for depth 15, residue 25652. -/
theorem bounds_15_25652 : exactInterval 15 25652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25652 : oddCount 25652 15 = 5 ∧ acceleratedOrbit 15 25652 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25652) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25652.1, data_15_25652.2]

/-- Complete interval computation for depth 15, residue 25653. -/
theorem bounds_15_25653 : exactInterval 15 25653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25653 : oddCount 25653 15 = 5 ∧ acceleratedOrbit 15 25653 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25653) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25653.1, data_15_25653.2]

/-- Complete interval computation for depth 15, residue 25654. -/
theorem bounds_15_25654 : exactInterval 15 25654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25654 : oddCount 25654 15 = 9 ∧ acceleratedOrbit 15 25654 = 15412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25654) = 3 ^ 9 * m + 15412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25654.1, data_15_25654.2]

/-- Complete interval computation for depth 15, residue 25655. -/
theorem bounds_15_25655 : exactInterval 15 25655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25655 : oddCount 25655 15 = 9 ∧ acceleratedOrbit 15 25655 = 15412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25655) = 3 ^ 9 * m + 15412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25655.1, data_15_25655.2]

/-- Complete interval computation for depth 15, residue 25656. -/
theorem bounds_15_25656 : exactInterval 15 25656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25656 : oddCount 25656 15 = 7 ∧ acceleratedOrbit 15 25656 = 1714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25656) = 3 ^ 7 * m + 1714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25656.1, data_15_25656.2]

end Collatz.Research.PassageAtlas.Batch0783
