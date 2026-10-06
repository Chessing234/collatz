import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0571

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18677. -/
theorem bounds_15_18677 : exactInterval 15 18677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18677 : oddCount 18677 15 = 6 ∧ acceleratedOrbit 15 18677 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18677) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18677.1, data_15_18677.2]

/-- Complete interval computation for depth 15, residue 18678. -/
theorem bounds_15_18678 : exactInterval 15 18678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18678 : oddCount 18678 15 = 7 ∧ acceleratedOrbit 15 18678 = 1247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18678) = 3 ^ 7 * m + 1247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18678.1, data_15_18678.2]

/-- Complete interval computation for depth 15, residue 18679. -/
theorem bounds_15_18679 : exactInterval 15 18679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18679 : oddCount 18679 15 = 7 ∧ acceleratedOrbit 15 18679 = 1247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18679) = 3 ^ 7 * m + 1247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18679.1, data_15_18679.2]

/-- Complete interval computation for depth 15, residue 18680. -/
theorem bounds_15_18680 : exactInterval 15 18680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18680 : oddCount 18680 15 = 8 ∧ acceleratedOrbit 15 18680 = 3743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18680) = 3 ^ 8 * m + 3743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18680.1, data_15_18680.2]

/-- Complete interval computation for depth 15, residue 18681. -/
theorem bounds_15_18681 : exactInterval 15 18681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18681 : oddCount 18681 15 = 7 ∧ acceleratedOrbit 15 18681 = 1247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18681) = 3 ^ 7 * m + 1247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18681.1, data_15_18681.2]

/-- Complete interval computation for depth 15, residue 18682. -/
theorem bounds_15_18682 : exactInterval 15 18682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18682 : oddCount 18682 15 = 8 ∧ acceleratedOrbit 15 18682 = 3743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18682) = 3 ^ 8 * m + 3743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18682.1, data_15_18682.2]

/-- Complete interval computation for depth 15, residue 18683. -/
theorem bounds_15_18683 : exactInterval 15 18683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18683 : oddCount 18683 15 = 10 ∧ acceleratedOrbit 15 18683 = 33671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18683) = 3 ^ 10 * m + 33671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18683.1, data_15_18683.2]

/-- Complete interval computation for depth 15, residue 18684. -/
theorem bounds_15_18684 : exactInterval 15 18684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18684 : oddCount 18684 15 = 8 ∧ acceleratedOrbit 15 18684 = 3743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18684) = 3 ^ 8 * m + 3743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18684.1, data_15_18684.2]

/-- Complete interval computation for depth 15, residue 18685. -/
theorem bounds_15_18685 : exactInterval 15 18685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18685 : oddCount 18685 15 = 8 ∧ acceleratedOrbit 15 18685 = 3743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18685) = 3 ^ 8 * m + 3743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18685.1, data_15_18685.2]

/-- Complete interval computation for depth 15, residue 18686. -/
theorem bounds_15_18686 : exactInterval 15 18686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18686 : oddCount 18686 15 = 10 ∧ acceleratedOrbit 15 18686 = 33677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18686) = 3 ^ 10 * m + 33677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18686.1, data_15_18686.2]

/-- Complete interval computation for depth 15, residue 18687. -/
theorem bounds_15_18687 : exactInterval 15 18687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18687 : oddCount 18687 15 = 10 ∧ acceleratedOrbit 15 18687 = 33677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18687) = 3 ^ 10 * m + 33677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18687.1, data_15_18687.2]

/-- Complete interval computation for depth 15, residue 18688. -/
theorem bounds_15_18688 : exactInterval 15 18688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18688 : oddCount 18688 15 = 4 ∧ acceleratedOrbit 15 18688 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18688) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18688.1, data_15_18688.2]

/-- Complete interval computation for depth 15, residue 18689. -/
theorem bounds_15_18689 : exactInterval 15 18689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18689 : oddCount 18689 15 = 6 ∧ acceleratedOrbit 15 18689 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18689) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18689.1, data_15_18689.2]

/-- Complete interval computation for depth 15, residue 18690. -/
theorem bounds_15_18690 : exactInterval 15 18690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18690 : oddCount 18690 15 = 10 ∧ acceleratedOrbit 15 18690 = 33695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18690) = 3 ^ 10 * m + 33695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18690.1, data_15_18690.2]

/-- Complete interval computation for depth 15, residue 18691. -/
theorem bounds_15_18691 : exactInterval 15 18691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18691 : oddCount 18691 15 = 10 ∧ acceleratedOrbit 15 18691 = 33695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18691) = 3 ^ 10 * m + 33695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18691.1, data_15_18691.2]

/-- Complete interval computation for depth 15, residue 18692. -/
theorem bounds_15_18692 : exactInterval 15 18692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18692 : oddCount 18692 15 = 5 ∧ acceleratedOrbit 15 18692 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18692) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18692.1, data_15_18692.2]

/-- Complete interval computation for depth 15, residue 18693. -/
theorem bounds_15_18693 : exactInterval 15 18693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18693 : oddCount 18693 15 = 5 ∧ acceleratedOrbit 15 18693 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18693) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18693.1, data_15_18693.2]

/-- Complete interval computation for depth 15, residue 18694. -/
theorem bounds_15_18694 : exactInterval 15 18694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18694 : oddCount 18694 15 = 5 ∧ acceleratedOrbit 15 18694 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18694) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18694.1, data_15_18694.2]

/-- Complete interval computation for depth 15, residue 18695. -/
theorem bounds_15_18695 : exactInterval 15 18695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18695 : oddCount 18695 15 = 10 ∧ acceleratedOrbit 15 18695 = 33695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18695) = 3 ^ 10 * m + 33695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18695.1, data_15_18695.2]

/-- Complete interval computation for depth 15, residue 18696. -/
theorem bounds_15_18696 : exactInterval 15 18696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18696 : oddCount 18696 15 = 5 ∧ acceleratedOrbit 15 18696 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18696) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18696.1, data_15_18696.2]

/-- Complete interval computation for depth 15, residue 18697. -/
theorem bounds_15_18697 : exactInterval 15 18697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18697 : oddCount 18697 15 = 6 ∧ acceleratedOrbit 15 18697 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18697) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18697.1, data_15_18697.2]

/-- Complete interval computation for depth 15, residue 18698. -/
theorem bounds_15_18698 : exactInterval 15 18698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18698 : oddCount 18698 15 = 5 ∧ acceleratedOrbit 15 18698 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18698) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18698.1, data_15_18698.2]

/-- Complete interval computation for depth 15, residue 18699. -/
theorem bounds_15_18699 : exactInterval 15 18699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18699 : oddCount 18699 15 = 8 ∧ acceleratedOrbit 15 18699 = 3746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18699) = 3 ^ 8 * m + 3746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18699.1, data_15_18699.2]

/-- Complete interval computation for depth 15, residue 18700. -/
theorem bounds_15_18700 : exactInterval 15 18700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18700 : oddCount 18700 15 = 5 ∧ acceleratedOrbit 15 18700 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18700) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18700.1, data_15_18700.2]

/-- Complete interval computation for depth 15, residue 18701. -/
theorem bounds_15_18701 : exactInterval 15 18701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18701 : oddCount 18701 15 = 5 ∧ acceleratedOrbit 15 18701 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18701) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18701.1, data_15_18701.2]

/-- Complete interval computation for depth 15, residue 18702. -/
theorem bounds_15_18702 : exactInterval 15 18702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18702 : oddCount 18702 15 = 8 ∧ acceleratedOrbit 15 18702 = 3746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18702) = 3 ^ 8 * m + 3746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18702.1, data_15_18702.2]

/-- Complete interval computation for depth 15, residue 18703. -/
theorem bounds_15_18703 : exactInterval 15 18703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18703 : oddCount 18703 15 = 8 ∧ acceleratedOrbit 15 18703 = 3746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18703) = 3 ^ 8 * m + 3746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18703.1, data_15_18703.2]

/-- Complete interval computation for depth 15, residue 18704. -/
theorem bounds_15_18704 : exactInterval 15 18704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18704 : oddCount 18704 15 = 6 ∧ acceleratedOrbit 15 18704 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18704) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18704.1, data_15_18704.2]

/-- Complete interval computation for depth 15, residue 18705. -/
theorem bounds_15_18705 : exactInterval 15 18705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18705 : oddCount 18705 15 = 5 ∧ acceleratedOrbit 15 18705 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18705) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18705.1, data_15_18705.2]

/-- Complete interval computation for depth 15, residue 18706. -/
theorem bounds_15_18706 : exactInterval 15 18706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18706 : oddCount 18706 15 = 10 ∧ acceleratedOrbit 15 18706 = 33716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18706) = 3 ^ 10 * m + 33716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18706.1, data_15_18706.2]

/-- Complete interval computation for depth 15, residue 18707. -/
theorem bounds_15_18707 : exactInterval 15 18707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18707 : oddCount 18707 15 = 10 ∧ acceleratedOrbit 15 18707 = 33716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18707) = 3 ^ 10 * m + 33716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18707.1, data_15_18707.2]

/-- Complete interval computation for depth 15, residue 18708. -/
theorem bounds_15_18708 : exactInterval 15 18708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18708 : oddCount 18708 15 = 6 ∧ acceleratedOrbit 15 18708 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18708) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18708.1, data_15_18708.2]

/-- Complete interval computation for depth 15, residue 18709. -/
theorem bounds_15_18709 : exactInterval 15 18709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18709 : oddCount 18709 15 = 6 ∧ acceleratedOrbit 15 18709 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18709) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18709.1, data_15_18709.2]

end Collatz.Research.PassageAtlas.Batch0571
