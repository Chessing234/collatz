import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0264

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8617. -/
theorem bounds_15_8617 : exactInterval 15 8617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8617 : oddCount 8617 15 = 11 ∧ acceleratedOrbit 15 8617 = 46595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8617) = 3 ^ 11 * m + 46595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8617.1, data_15_8617.2]

/-- Complete interval computation for depth 15, residue 8618. -/
theorem bounds_15_8618 : exactInterval 15 8618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8618 : oddCount 8618 15 = 4 ∧ acceleratedOrbit 15 8618 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8618) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8618.1, data_15_8618.2]

/-- Complete interval computation for depth 15, residue 8619. -/
theorem bounds_15_8619 : exactInterval 15 8619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8619 : oddCount 8619 15 = 9 ∧ acceleratedOrbit 15 8619 = 5179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8619) = 3 ^ 9 * m + 5179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8619.1, data_15_8619.2]

/-- Complete interval computation for depth 15, residue 8620. -/
theorem bounds_15_8620 : exactInterval 15 8620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8620 : oddCount 8620 15 = 10 ∧ acceleratedOrbit 15 8620 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8620) = 3 ^ 10 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8620.1, data_15_8620.2]

/-- Complete interval computation for depth 15, residue 8621. -/
theorem bounds_15_8621 : exactInterval 15 8621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8621 : oddCount 8621 15 = 10 ∧ acceleratedOrbit 15 8621 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8621) = 3 ^ 10 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8621.1, data_15_8621.2]

/-- Complete interval computation for depth 15, residue 8622. -/
theorem bounds_15_8622 : exactInterval 15 8622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8622 : oddCount 8622 15 = 10 ∧ acceleratedOrbit 15 8622 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8622) = 3 ^ 10 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8622.1, data_15_8622.2]

/-- Complete interval computation for depth 15, residue 8623. -/
theorem bounds_15_8623 : exactInterval 15 8623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8623 : oddCount 8623 15 = 9 ∧ acceleratedOrbit 15 8623 = 5183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8623) = 3 ^ 9 * m + 5183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8623.1, data_15_8623.2]

/-- Complete interval computation for depth 15, residue 8624. -/
theorem bounds_15_8624 : exactInterval 15 8624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8624 : oddCount 8624 15 = 7 ∧ acceleratedOrbit 15 8624 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8624) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8624.1, data_15_8624.2]

/-- Complete interval computation for depth 15, residue 8625. -/
theorem bounds_15_8625 : exactInterval 15 8625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8625 : oddCount 8625 15 = 7 ∧ acceleratedOrbit 15 8625 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8625) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8625.1, data_15_8625.2]

/-- Complete interval computation for depth 15, residue 8626. -/
theorem bounds_15_8626 : exactInterval 15 8626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8626 : oddCount 8626 15 = 7 ∧ acceleratedOrbit 15 8626 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8626) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8626.1, data_15_8626.2]

/-- Complete interval computation for depth 15, residue 8627. -/
theorem bounds_15_8627 : exactInterval 15 8627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8627 : oddCount 8627 15 = 7 ∧ acceleratedOrbit 15 8627 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8627) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8627.1, data_15_8627.2]

/-- Complete interval computation for depth 15, residue 8628. -/
theorem bounds_15_8628 : exactInterval 15 8628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8628 : oddCount 8628 15 = 7 ∧ acceleratedOrbit 15 8628 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8628) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8628.1, data_15_8628.2]

/-- Complete interval computation for depth 15, residue 8629. -/
theorem bounds_15_8629 : exactInterval 15 8629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8629 : oddCount 8629 15 = 7 ∧ acceleratedOrbit 15 8629 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8629) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8629.1, data_15_8629.2]

/-- Complete interval computation for depth 15, residue 8630. -/
theorem bounds_15_8630 : exactInterval 15 8630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8630 : oddCount 8630 15 = 8 ∧ acceleratedOrbit 15 8630 = 1729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8630) = 3 ^ 8 * m + 1729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8630.1, data_15_8630.2]

/-- Complete interval computation for depth 15, residue 8631. -/
theorem bounds_15_8631 : exactInterval 15 8631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8631 : oddCount 8631 15 = 8 ∧ acceleratedOrbit 15 8631 = 1729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8631) = 3 ^ 8 * m + 1729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8631.1, data_15_8631.2]

/-- Complete interval computation for depth 15, residue 8632. -/
theorem bounds_15_8632 : exactInterval 15 8632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8632 : oddCount 8632 15 = 7 ∧ acceleratedOrbit 15 8632 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8632) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8632.1, data_15_8632.2]

/-- Complete interval computation for depth 15, residue 8633. -/
theorem bounds_15_8633 : exactInterval 15 8633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8633 : oddCount 8633 15 = 7 ∧ acceleratedOrbit 15 8633 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8633) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8633.1, data_15_8633.2]

/-- Complete interval computation for depth 15, residue 8634. -/
theorem bounds_15_8634 : exactInterval 15 8634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8634 : oddCount 8634 15 = 7 ∧ acceleratedOrbit 15 8634 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8634) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8634.1, data_15_8634.2]

/-- Complete interval computation for depth 15, residue 8635. -/
theorem bounds_15_8635 : exactInterval 15 8635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8635 : oddCount 8635 15 = 8 ∧ acceleratedOrbit 15 8635 = 1730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8635) = 3 ^ 8 * m + 1730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8635.1, data_15_8635.2]

/-- Complete interval computation for depth 15, residue 8636. -/
theorem bounds_15_8636 : exactInterval 15 8636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8636 : oddCount 8636 15 = 10 ∧ acceleratedOrbit 15 8636 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8636) = 3 ^ 10 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8636.1, data_15_8636.2]

/-- Complete interval computation for depth 15, residue 8637. -/
theorem bounds_15_8637 : exactInterval 15 8637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8637 : oddCount 8637 15 = 10 ∧ acceleratedOrbit 15 8637 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8637) = 3 ^ 10 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8637.1, data_15_8637.2]

/-- Complete interval computation for depth 15, residue 8638. -/
theorem bounds_15_8638 : exactInterval 15 8638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8638 : oddCount 8638 15 = 10 ∧ acceleratedOrbit 15 8638 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8638) = 3 ^ 10 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8638.1, data_15_8638.2]

/-- Complete interval computation for depth 15, residue 8639. -/
theorem bounds_15_8639 : exactInterval 15 8639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8639 : oddCount 8639 15 = 12 ∧ acceleratedOrbit 15 8639 = 140129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8639) = 3 ^ 12 * m + 140129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8639.1, data_15_8639.2]

/-- Complete interval computation for depth 15, residue 8640. -/
theorem bounds_15_8640 : exactInterval 15 8640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8640 : oddCount 8640 15 = 5 ∧ acceleratedOrbit 15 8640 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8640) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8640.1, data_15_8640.2]

/-- Complete interval computation for depth 15, residue 8641. -/
theorem bounds_15_8641 : exactInterval 15 8641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8641 : oddCount 8641 15 = 9 ∧ acceleratedOrbit 15 8641 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8641) = 3 ^ 9 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8641.1, data_15_8641.2]

/-- Complete interval computation for depth 15, residue 8642. -/
theorem bounds_15_8642 : exactInterval 15 8642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8642 : oddCount 8642 15 = 9 ∧ acceleratedOrbit 15 8642 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8642) = 3 ^ 9 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8642.1, data_15_8642.2]

/-- Complete interval computation for depth 15, residue 8643. -/
theorem bounds_15_8643 : exactInterval 15 8643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8643 : oddCount 8643 15 = 9 ∧ acceleratedOrbit 15 8643 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8643) = 3 ^ 9 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8643.1, data_15_8643.2]

/-- Complete interval computation for depth 15, residue 8644. -/
theorem bounds_15_8644 : exactInterval 15 8644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8644 : oddCount 8644 15 = 4 ∧ acceleratedOrbit 15 8644 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8644) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8644.1, data_15_8644.2]

/-- Complete interval computation for depth 15, residue 8645. -/
theorem bounds_15_8645 : exactInterval 15 8645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8645 : oddCount 8645 15 = 4 ∧ acceleratedOrbit 15 8645 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8645) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8645.1, data_15_8645.2]

/-- Complete interval computation for depth 15, residue 8646. -/
theorem bounds_15_8646 : exactInterval 15 8646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8646 : oddCount 8646 15 = 4 ∧ acceleratedOrbit 15 8646 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8646) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8646.1, data_15_8646.2]

/-- Complete interval computation for depth 15, residue 8647. -/
theorem bounds_15_8647 : exactInterval 15 8647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8647 : oddCount 8647 15 = 8 ∧ acceleratedOrbit 15 8647 = 1732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8647) = 3 ^ 8 * m + 1732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8647.1, data_15_8647.2]

/-- Complete interval computation for depth 15, residue 8648. -/
theorem bounds_15_8648 : exactInterval 15 8648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8648 : oddCount 8648 15 = 6 ∧ acceleratedOrbit 15 8648 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8648) = 3 ^ 6 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8648.1, data_15_8648.2]

/-- Complete interval computation for depth 15, residue 8649. -/
theorem bounds_15_8649 : exactInterval 15 8649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8649 : oddCount 8649 15 = 7 ∧ acceleratedOrbit 15 8649 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8649) = 3 ^ 7 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8649.1, data_15_8649.2]

end Collatz.Research.PassageAtlas.Batch0264
