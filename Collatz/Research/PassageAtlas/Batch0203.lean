import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0203

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6619. -/
theorem bounds_15_6619 : exactInterval 15 6619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6619 : oddCount 6619 15 = 7 ∧ acceleratedOrbit 15 6619 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6619) = 3 ^ 7 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6619.1, data_15_6619.2]

/-- Complete interval computation for depth 15, residue 6620. -/
theorem bounds_15_6620 : exactInterval 15 6620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6620 : oddCount 6620 15 = 6 ∧ acceleratedOrbit 15 6620 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6620) = 3 ^ 6 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6620.1, data_15_6620.2]

/-- Complete interval computation for depth 15, residue 6621. -/
theorem bounds_15_6621 : exactInterval 15 6621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6621 : oddCount 6621 15 = 6 ∧ acceleratedOrbit 15 6621 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6621) = 3 ^ 6 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6621.1, data_15_6621.2]

/-- Complete interval computation for depth 15, residue 6622. -/
theorem bounds_15_6622 : exactInterval 15 6622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6622 : oddCount 6622 15 = 11 ∧ acceleratedOrbit 15 6622 = 35812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6622) = 3 ^ 11 * m + 35812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6622.1, data_15_6622.2]

/-- Complete interval computation for depth 15, residue 6623. -/
theorem bounds_15_6623 : exactInterval 15 6623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6623 : oddCount 6623 15 = 11 ∧ acceleratedOrbit 15 6623 = 35812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6623) = 3 ^ 11 * m + 35812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6623.1, data_15_6623.2]

/-- Complete interval computation for depth 15, residue 6624. -/
theorem bounds_15_6624 : exactInterval 15 6624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6624 : oddCount 6624 15 = 7 ∧ acceleratedOrbit 15 6624 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6624) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6624.1, data_15_6624.2]

/-- Complete interval computation for depth 15, residue 6625. -/
theorem bounds_15_6625 : exactInterval 15 6625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6625 : oddCount 6625 15 = 9 ∧ acceleratedOrbit 15 6625 = 3982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6625) = 3 ^ 9 * m + 3982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6625.1, data_15_6625.2]

/-- Complete interval computation for depth 15, residue 6626. -/
theorem bounds_15_6626 : exactInterval 15 6626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6626 : oddCount 6626 15 = 7 ∧ acceleratedOrbit 15 6626 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6626) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6626.1, data_15_6626.2]

/-- Complete interval computation for depth 15, residue 6627. -/
theorem bounds_15_6627 : exactInterval 15 6627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6627 : oddCount 6627 15 = 7 ∧ acceleratedOrbit 15 6627 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6627) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6627.1, data_15_6627.2]

/-- Complete interval computation for depth 15, residue 6628. -/
theorem bounds_15_6628 : exactInterval 15 6628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6628 : oddCount 6628 15 = 7 ∧ acceleratedOrbit 15 6628 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6628) = 3 ^ 7 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6628.1, data_15_6628.2]

/-- Complete interval computation for depth 15, residue 6629. -/
theorem bounds_15_6629 : exactInterval 15 6629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6629 : oddCount 6629 15 = 7 ∧ acceleratedOrbit 15 6629 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6629) = 3 ^ 7 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6629.1, data_15_6629.2]

/-- Complete interval computation for depth 15, residue 6630. -/
theorem bounds_15_6630 : exactInterval 15 6630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6630 : oddCount 6630 15 = 7 ∧ acceleratedOrbit 15 6630 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6630) = 3 ^ 7 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6630.1, data_15_6630.2]

/-- Complete interval computation for depth 15, residue 6631. -/
theorem bounds_15_6631 : exactInterval 15 6631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6631 : oddCount 6631 15 = 8 ∧ acceleratedOrbit 15 6631 = 1328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6631) = 3 ^ 8 * m + 1328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6631.1, data_15_6631.2]

/-- Complete interval computation for depth 15, residue 6632. -/
theorem bounds_15_6632 : exactInterval 15 6632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6632 : oddCount 6632 15 = 7 ∧ acceleratedOrbit 15 6632 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6632) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6632.1, data_15_6632.2]

/-- Complete interval computation for depth 15, residue 6633. -/
theorem bounds_15_6633 : exactInterval 15 6633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6633 : oddCount 6633 15 = 9 ∧ acceleratedOrbit 15 6633 = 3986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6633) = 3 ^ 9 * m + 3986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6633.1, data_15_6633.2]

/-- Complete interval computation for depth 15, residue 6634. -/
theorem bounds_15_6634 : exactInterval 15 6634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6634 : oddCount 6634 15 = 7 ∧ acceleratedOrbit 15 6634 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6634) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6634.1, data_15_6634.2]

/-- Complete interval computation for depth 15, residue 6635. -/
theorem bounds_15_6635 : exactInterval 15 6635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6635 : oddCount 6635 15 = 11 ∧ acceleratedOrbit 15 6635 = 35882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6635) = 3 ^ 11 * m + 35882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6635.1, data_15_6635.2]

/-- Complete interval computation for depth 15, residue 6636. -/
theorem bounds_15_6636 : exactInterval 15 6636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6636 : oddCount 6636 15 = 6 ∧ acceleratedOrbit 15 6636 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6636) = 3 ^ 6 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6636.1, data_15_6636.2]

/-- Complete interval computation for depth 15, residue 6637. -/
theorem bounds_15_6637 : exactInterval 15 6637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6637 : oddCount 6637 15 = 6 ∧ acceleratedOrbit 15 6637 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6637) = 3 ^ 6 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6637.1, data_15_6637.2]

/-- Complete interval computation for depth 15, residue 6638. -/
theorem bounds_15_6638 : exactInterval 15 6638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6638 : oddCount 6638 15 = 6 ∧ acceleratedOrbit 15 6638 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6638) = 3 ^ 6 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6638.1, data_15_6638.2]

/-- Complete interval computation for depth 15, residue 6639. -/
theorem bounds_15_6639 : exactInterval 15 6639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6639 : oddCount 6639 15 = 10 ∧ acceleratedOrbit 15 6639 = 11966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6639) = 3 ^ 10 * m + 11966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6639.1, data_15_6639.2]

/-- Complete interval computation for depth 15, residue 6640. -/
theorem bounds_15_6640 : exactInterval 15 6640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6640 : oddCount 6640 15 = 8 ∧ acceleratedOrbit 15 6640 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6640) = 3 ^ 8 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6640.1, data_15_6640.2]

/-- Complete interval computation for depth 15, residue 6641. -/
theorem bounds_15_6641 : exactInterval 15 6641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6641 : oddCount 6641 15 = 7 ∧ acceleratedOrbit 15 6641 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6641) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6641.1, data_15_6641.2]

/-- Complete interval computation for depth 15, residue 6642. -/
theorem bounds_15_6642 : exactInterval 15 6642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6642 : oddCount 6642 15 = 9 ∧ acceleratedOrbit 15 6642 = 3995 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6642) = 3 ^ 9 * m + 3995 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6642.1, data_15_6642.2]

/-- Complete interval computation for depth 15, residue 6643. -/
theorem bounds_15_6643 : exactInterval 15 6643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6643 : oddCount 6643 15 = 9 ∧ acceleratedOrbit 15 6643 = 3995 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6643) = 3 ^ 9 * m + 3995 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6643.1, data_15_6643.2]

/-- Complete interval computation for depth 15, residue 6644. -/
theorem bounds_15_6644 : exactInterval 15 6644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6644 : oddCount 6644 15 = 8 ∧ acceleratedOrbit 15 6644 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6644) = 3 ^ 8 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6644.1, data_15_6644.2]

/-- Complete interval computation for depth 15, residue 6645. -/
theorem bounds_15_6645 : exactInterval 15 6645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6645 : oddCount 6645 15 = 8 ∧ acceleratedOrbit 15 6645 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6645) = 3 ^ 8 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6645.1, data_15_6645.2]

/-- Complete interval computation for depth 15, residue 6646. -/
theorem bounds_15_6646 : exactInterval 15 6646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6646 : oddCount 6646 15 = 10 ∧ acceleratedOrbit 15 6646 = 11983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6646) = 3 ^ 10 * m + 11983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6646.1, data_15_6646.2]

/-- Complete interval computation for depth 15, residue 6647. -/
theorem bounds_15_6647 : exactInterval 15 6647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6647 : oddCount 6647 15 = 10 ∧ acceleratedOrbit 15 6647 = 11983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6647) = 3 ^ 10 * m + 11983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6647.1, data_15_6647.2]

/-- Complete interval computation for depth 15, residue 6648. -/
theorem bounds_15_6648 : exactInterval 15 6648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6648 : oddCount 6648 15 = 8 ∧ acceleratedOrbit 15 6648 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6648) = 3 ^ 8 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6648.1, data_15_6648.2]

/-- Complete interval computation for depth 15, residue 6649. -/
theorem bounds_15_6649 : exactInterval 15 6649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6649 : oddCount 6649 15 = 11 ∧ acceleratedOrbit 15 6649 = 35963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6649) = 3 ^ 11 * m + 35963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6649.1, data_15_6649.2]

/-- Complete interval computation for depth 15, residue 6650. -/
theorem bounds_15_6650 : exactInterval 15 6650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6650 : oddCount 6650 15 = 8 ∧ acceleratedOrbit 15 6650 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6650) = 3 ^ 8 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6650.1, data_15_6650.2]

end Collatz.Research.PassageAtlas.Batch0203
