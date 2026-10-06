import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0146

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4751. -/
theorem bounds_15_4751 : exactInterval 15 4751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4751 : oddCount 4751 15 = 11 ∧ acceleratedOrbit 15 4751 = 25697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4751) = 3 ^ 11 * m + 25697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4751.1, data_15_4751.2]

/-- Complete interval computation for depth 15, residue 4752. -/
theorem bounds_15_4752 : exactInterval 15 4752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4752 : oddCount 4752 15 = 7 ∧ acceleratedOrbit 15 4752 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4752) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4752.1, data_15_4752.2]

/-- Complete interval computation for depth 15, residue 4753. -/
theorem bounds_15_4753 : exactInterval 15 4753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4753 : oddCount 4753 15 = 9 ∧ acceleratedOrbit 15 4753 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4753) = 3 ^ 9 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4753.1, data_15_4753.2]

/-- Complete interval computation for depth 15, residue 4754. -/
theorem bounds_15_4754 : exactInterval 15 4754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4754 : oddCount 4754 15 = 9 ∧ acceleratedOrbit 15 4754 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4754) = 3 ^ 9 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4754.1, data_15_4754.2]

/-- Complete interval computation for depth 15, residue 4755. -/
theorem bounds_15_4755 : exactInterval 15 4755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4755 : oddCount 4755 15 = 9 ∧ acceleratedOrbit 15 4755 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4755) = 3 ^ 9 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4755.1, data_15_4755.2]

/-- Complete interval computation for depth 15, residue 4756. -/
theorem bounds_15_4756 : exactInterval 15 4756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4756 : oddCount 4756 15 = 7 ∧ acceleratedOrbit 15 4756 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4756) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4756.1, data_15_4756.2]

/-- Complete interval computation for depth 15, residue 4757. -/
theorem bounds_15_4757 : exactInterval 15 4757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4757 : oddCount 4757 15 = 7 ∧ acceleratedOrbit 15 4757 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4757) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4757.1, data_15_4757.2]

/-- Complete interval computation for depth 15, residue 4758. -/
theorem bounds_15_4758 : exactInterval 15 4758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4758 : oddCount 4758 15 = 7 ∧ acceleratedOrbit 15 4758 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4758) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4758.1, data_15_4758.2]

/-- Complete interval computation for depth 15, residue 4759. -/
theorem bounds_15_4759 : exactInterval 15 4759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4759 : oddCount 4759 15 = 7 ∧ acceleratedOrbit 15 4759 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4759) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4759.1, data_15_4759.2]

/-- Complete interval computation for depth 15, residue 4760. -/
theorem bounds_15_4760 : exactInterval 15 4760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4760 : oddCount 4760 15 = 7 ∧ acceleratedOrbit 15 4760 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4760) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4760.1, data_15_4760.2]

/-- Complete interval computation for depth 15, residue 4761. -/
theorem bounds_15_4761 : exactInterval 15 4761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4761 : oddCount 4761 15 = 6 ∧ acceleratedOrbit 15 4761 = 106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4761) = 3 ^ 6 * m + 106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4761.1, data_15_4761.2]

/-- Complete interval computation for depth 15, residue 4762. -/
theorem bounds_15_4762 : exactInterval 15 4762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4762 : oddCount 4762 15 = 7 ∧ acceleratedOrbit 15 4762 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4762) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4762.1, data_15_4762.2]

/-- Complete interval computation for depth 15, residue 4763. -/
theorem bounds_15_4763 : exactInterval 15 4763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4763 : oddCount 4763 15 = 13 ∧ acceleratedOrbit 15 4763 = 231821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4763) = 3 ^ 13 * m + 231821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4763.1, data_15_4763.2]

/-- Complete interval computation for depth 15, residue 4764. -/
theorem bounds_15_4764 : exactInterval 15 4764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4764 : oddCount 4764 15 = 8 ∧ acceleratedOrbit 15 4764 = 955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4764) = 3 ^ 8 * m + 955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4764.1, data_15_4764.2]

/-- Complete interval computation for depth 15, residue 4765. -/
theorem bounds_15_4765 : exactInterval 15 4765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4765 : oddCount 4765 15 = 8 ∧ acceleratedOrbit 15 4765 = 955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4765) = 3 ^ 8 * m + 955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4765.1, data_15_4765.2]

/-- Complete interval computation for depth 15, residue 4766. -/
theorem bounds_15_4766 : exactInterval 15 4766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4766 : oddCount 4766 15 = 8 ∧ acceleratedOrbit 15 4766 = 955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4766) = 3 ^ 8 * m + 955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4766.1, data_15_4766.2]

/-- Complete interval computation for depth 15, residue 4767. -/
theorem bounds_15_4767 : exactInterval 15 4767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4767 : oddCount 4767 15 = 11 ∧ acceleratedOrbit 15 4767 = 25778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4767) = 3 ^ 11 * m + 25778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4767.1, data_15_4767.2]

/-- Complete interval computation for depth 15, residue 4768. -/
theorem bounds_15_4768 : exactInterval 15 4768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4768 : oddCount 4768 15 = 4 ∧ acceleratedOrbit 15 4768 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4768) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4768.1, data_15_4768.2]

/-- Complete interval computation for depth 15, residue 4769. -/
theorem bounds_15_4769 : exactInterval 15 4769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4769 : oddCount 4769 15 = 8 ∧ acceleratedOrbit 15 4769 = 956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4769) = 3 ^ 8 * m + 956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4769.1, data_15_4769.2]

/-- Complete interval computation for depth 15, residue 4770. -/
theorem bounds_15_4770 : exactInterval 15 4770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4770 : oddCount 4770 15 = 10 ∧ acceleratedOrbit 15 4770 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4770) = 3 ^ 10 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4770.1, data_15_4770.2]

/-- Complete interval computation for depth 15, residue 4771. -/
theorem bounds_15_4771 : exactInterval 15 4771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4771 : oddCount 4771 15 = 10 ∧ acceleratedOrbit 15 4771 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4771) = 3 ^ 10 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4771.1, data_15_4771.2]

/-- Complete interval computation for depth 15, residue 4772. -/
theorem bounds_15_4772 : exactInterval 15 4772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4772 : oddCount 4772 15 = 10 ∧ acceleratedOrbit 15 4772 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4772) = 3 ^ 10 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4772.1, data_15_4772.2]

/-- Complete interval computation for depth 15, residue 4773. -/
theorem bounds_15_4773 : exactInterval 15 4773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4773 : oddCount 4773 15 = 10 ∧ acceleratedOrbit 15 4773 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4773) = 3 ^ 10 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4773.1, data_15_4773.2]

/-- Complete interval computation for depth 15, residue 4774. -/
theorem bounds_15_4774 : exactInterval 15 4774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4774 : oddCount 4774 15 = 10 ∧ acceleratedOrbit 15 4774 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4774) = 3 ^ 10 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4774.1, data_15_4774.2]

/-- Complete interval computation for depth 15, residue 4775. -/
theorem bounds_15_4775 : exactInterval 15 4775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4775 : oddCount 4775 15 = 10 ∧ acceleratedOrbit 15 4775 = 8608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4775) = 3 ^ 10 * m + 8608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4775.1, data_15_4775.2]

/-- Complete interval computation for depth 15, residue 4776. -/
theorem bounds_15_4776 : exactInterval 15 4776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4776 : oddCount 4776 15 = 4 ∧ acceleratedOrbit 15 4776 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4776) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4776.1, data_15_4776.2]

/-- Complete interval computation for depth 15, residue 4777. -/
theorem bounds_15_4777 : exactInterval 15 4777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4777 : oddCount 4777 15 = 11 ∧ acceleratedOrbit 15 4777 = 25834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4777) = 3 ^ 11 * m + 25834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4777.1, data_15_4777.2]

/-- Complete interval computation for depth 15, residue 4778. -/
theorem bounds_15_4778 : exactInterval 15 4778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4778 : oddCount 4778 15 = 4 ∧ acceleratedOrbit 15 4778 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4778) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4778.1, data_15_4778.2]

/-- Complete interval computation for depth 15, residue 4779. -/
theorem bounds_15_4779 : exactInterval 15 4779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4779 : oddCount 4779 15 = 8 ∧ acceleratedOrbit 15 4779 = 958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4779) = 3 ^ 8 * m + 958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4779.1, data_15_4779.2]

/-- Complete interval computation for depth 15, residue 4780. -/
theorem bounds_15_4780 : exactInterval 15 4780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4780 : oddCount 4780 15 = 6 ∧ acceleratedOrbit 15 4780 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4780) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4780.1, data_15_4780.2]

/-- Complete interval computation for depth 15, residue 4781. -/
theorem bounds_15_4781 : exactInterval 15 4781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4781 : oddCount 4781 15 = 6 ∧ acceleratedOrbit 15 4781 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4781) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4781.1, data_15_4781.2]

/-- Complete interval computation for depth 15, residue 4782. -/
theorem bounds_15_4782 : exactInterval 15 4782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4782 : oddCount 4782 15 = 6 ∧ acceleratedOrbit 15 4782 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4782) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4782.1, data_15_4782.2]

/-- Complete interval computation for depth 15, residue 4783. -/
theorem bounds_15_4783 : exactInterval 15 4783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4783 : oddCount 4783 15 = 9 ∧ acceleratedOrbit 15 4783 = 2875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4783) = 3 ^ 9 * m + 2875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4783.1, data_15_4783.2]

end Collatz.Research.PassageAtlas.Batch0146
