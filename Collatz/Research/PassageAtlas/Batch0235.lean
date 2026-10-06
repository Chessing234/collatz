import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0235

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7667. -/
theorem bounds_15_7667 : exactInterval 15 7667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7667 : oddCount 7667 15 = 8 ∧ acceleratedOrbit 15 7667 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7667) = 3 ^ 8 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7667.1, data_15_7667.2]

/-- Complete interval computation for depth 15, residue 7668. -/
theorem bounds_15_7668 : exactInterval 15 7668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7668 : oddCount 7668 15 = 9 ∧ acceleratedOrbit 15 7668 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7668) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7668.1, data_15_7668.2]

/-- Complete interval computation for depth 15, residue 7669. -/
theorem bounds_15_7669 : exactInterval 15 7669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7669 : oddCount 7669 15 = 9 ∧ acceleratedOrbit 15 7669 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7669) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7669.1, data_15_7669.2]

/-- Complete interval computation for depth 15, residue 7670. -/
theorem bounds_15_7670 : exactInterval 15 7670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7670 : oddCount 7670 15 = 9 ∧ acceleratedOrbit 15 7670 = 4610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7670) = 3 ^ 9 * m + 4610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7670.1, data_15_7670.2]

/-- Complete interval computation for depth 15, residue 7671. -/
theorem bounds_15_7671 : exactInterval 15 7671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7671 : oddCount 7671 15 = 9 ∧ acceleratedOrbit 15 7671 = 4610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7671) = 3 ^ 9 * m + 4610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7671.1, data_15_7671.2]

/-- Complete interval computation for depth 15, residue 7672. -/
theorem bounds_15_7672 : exactInterval 15 7672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7672 : oddCount 7672 15 = 10 ∧ acceleratedOrbit 15 7672 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7672) = 3 ^ 10 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7672.1, data_15_7672.2]

/-- Complete interval computation for depth 15, residue 7673. -/
theorem bounds_15_7673 : exactInterval 15 7673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7673 : oddCount 7673 15 = 8 ∧ acceleratedOrbit 15 7673 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7673) = 3 ^ 8 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7673.1, data_15_7673.2]

/-- Complete interval computation for depth 15, residue 7674. -/
theorem bounds_15_7674 : exactInterval 15 7674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7674 : oddCount 7674 15 = 10 ∧ acceleratedOrbit 15 7674 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7674) = 3 ^ 10 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7674.1, data_15_7674.2]

/-- Complete interval computation for depth 15, residue 7675. -/
theorem bounds_15_7675 : exactInterval 15 7675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7675 : oddCount 7675 15 = 9 ∧ acceleratedOrbit 15 7675 = 4612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7675) = 3 ^ 9 * m + 4612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7675.1, data_15_7675.2]

/-- Complete interval computation for depth 15, residue 7676. -/
theorem bounds_15_7676 : exactInterval 15 7676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7676 : oddCount 7676 15 = 10 ∧ acceleratedOrbit 15 7676 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7676) = 3 ^ 10 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7676.1, data_15_7676.2]

/-- Complete interval computation for depth 15, residue 7677. -/
theorem bounds_15_7677 : exactInterval 15 7677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7677 : oddCount 7677 15 = 10 ∧ acceleratedOrbit 15 7677 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7677) = 3 ^ 10 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7677.1, data_15_7677.2]

/-- Complete interval computation for depth 15, residue 7678. -/
theorem bounds_15_7678 : exactInterval 15 7678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7678 : oddCount 7678 15 = 11 ∧ acceleratedOrbit 15 7678 = 41519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7678) = 3 ^ 11 * m + 41519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7678.1, data_15_7678.2]

/-- Complete interval computation for depth 15, residue 7679. -/
theorem bounds_15_7679 : exactInterval 15 7679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7679 : oddCount 7679 15 = 11 ∧ acceleratedOrbit 15 7679 = 41519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7679) = 3 ^ 11 * m + 41519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7679.1, data_15_7679.2]

/-- Complete interval computation for depth 15, residue 7680. -/
theorem bounds_15_7680 : exactInterval 15 7680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7680 : oddCount 7680 15 = 4 ∧ acceleratedOrbit 15 7680 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7680) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7680.1, data_15_7680.2]

/-- Complete interval computation for depth 15, residue 7681. -/
theorem bounds_15_7681 : exactInterval 15 7681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7681 : oddCount 7681 15 = 11 ∧ acceleratedOrbit 15 7681 = 41552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7681) = 3 ^ 11 * m + 41552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7681.1, data_15_7681.2]

/-- Complete interval computation for depth 15, residue 7682. -/
theorem bounds_15_7682 : exactInterval 15 7682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7682 : oddCount 7682 15 = 4 ∧ acceleratedOrbit 15 7682 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7682) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7682.1, data_15_7682.2]

/-- Complete interval computation for depth 15, residue 7683. -/
theorem bounds_15_7683 : exactInterval 15 7683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7683 : oddCount 7683 15 = 4 ∧ acceleratedOrbit 15 7683 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7683) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7683.1, data_15_7683.2]

/-- Complete interval computation for depth 15, residue 7684. -/
theorem bounds_15_7684 : exactInterval 15 7684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7684 : oddCount 7684 15 = 7 ∧ acceleratedOrbit 15 7684 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7684) = 3 ^ 7 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7684.1, data_15_7684.2]

/-- Complete interval computation for depth 15, residue 7685. -/
theorem bounds_15_7685 : exactInterval 15 7685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7685 : oddCount 7685 15 = 7 ∧ acceleratedOrbit 15 7685 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7685) = 3 ^ 7 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7685.1, data_15_7685.2]

/-- Complete interval computation for depth 15, residue 7686. -/
theorem bounds_15_7686 : exactInterval 15 7686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7686 : oddCount 7686 15 = 7 ∧ acceleratedOrbit 15 7686 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7686) = 3 ^ 7 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7686.1, data_15_7686.2]

/-- Complete interval computation for depth 15, residue 7687. -/
theorem bounds_15_7687 : exactInterval 15 7687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7687 : oddCount 7687 15 = 8 ∧ acceleratedOrbit 15 7687 = 1540 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7687) = 3 ^ 8 * m + 1540 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7687.1, data_15_7687.2]

/-- Complete interval computation for depth 15, residue 7688. -/
theorem bounds_15_7688 : exactInterval 15 7688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7688 : oddCount 7688 15 = 6 ∧ acceleratedOrbit 15 7688 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7688) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7688.1, data_15_7688.2]

/-- Complete interval computation for depth 15, residue 7689. -/
theorem bounds_15_7689 : exactInterval 15 7689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7689 : oddCount 7689 15 = 8 ∧ acceleratedOrbit 15 7689 = 1541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7689) = 3 ^ 8 * m + 1541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7689.1, data_15_7689.2]

/-- Complete interval computation for depth 15, residue 7690. -/
theorem bounds_15_7690 : exactInterval 15 7690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7690 : oddCount 7690 15 = 6 ∧ acceleratedOrbit 15 7690 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7690) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7690.1, data_15_7690.2]

/-- Complete interval computation for depth 15, residue 7691. -/
theorem bounds_15_7691 : exactInterval 15 7691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7691 : oddCount 7691 15 = 7 ∧ acceleratedOrbit 15 7691 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7691) = 3 ^ 7 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7691.1, data_15_7691.2]

/-- Complete interval computation for depth 15, residue 7692. -/
theorem bounds_15_7692 : exactInterval 15 7692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7692 : oddCount 7692 15 = 6 ∧ acceleratedOrbit 15 7692 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7692) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7692.1, data_15_7692.2]

/-- Complete interval computation for depth 15, residue 7693. -/
theorem bounds_15_7693 : exactInterval 15 7693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7693 : oddCount 7693 15 = 6 ∧ acceleratedOrbit 15 7693 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7693) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7693.1, data_15_7693.2]

/-- Complete interval computation for depth 15, residue 7694. -/
theorem bounds_15_7694 : exactInterval 15 7694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7694 : oddCount 7694 15 = 7 ∧ acceleratedOrbit 15 7694 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7694) = 3 ^ 7 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7694.1, data_15_7694.2]

/-- Complete interval computation for depth 15, residue 7695. -/
theorem bounds_15_7695 : exactInterval 15 7695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7695 : oddCount 7695 15 = 7 ∧ acceleratedOrbit 15 7695 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7695) = 3 ^ 7 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7695.1, data_15_7695.2]

/-- Complete interval computation for depth 15, residue 7696. -/
theorem bounds_15_7696 : exactInterval 15 7696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7696 : oddCount 7696 15 = 6 ∧ acceleratedOrbit 15 7696 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7696) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7696.1, data_15_7696.2]

/-- Complete interval computation for depth 15, residue 7697. -/
theorem bounds_15_7697 : exactInterval 15 7697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7697 : oddCount 7697 15 = 6 ∧ acceleratedOrbit 15 7697 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7697) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7697.1, data_15_7697.2]

/-- Complete interval computation for depth 15, residue 7698. -/
theorem bounds_15_7698 : exactInterval 15 7698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7698 : oddCount 7698 15 = 9 ∧ acceleratedOrbit 15 7698 = 4627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7698) = 3 ^ 9 * m + 4627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7698.1, data_15_7698.2]

/-- Complete interval computation for depth 15, residue 7699. -/
theorem bounds_15_7699 : exactInterval 15 7699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7699 : oddCount 7699 15 = 9 ∧ acceleratedOrbit 15 7699 = 4627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7699) = 3 ^ 9 * m + 4627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7699.1, data_15_7699.2]

end Collatz.Research.PassageAtlas.Batch0235
