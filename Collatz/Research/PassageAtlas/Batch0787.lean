import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0787

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25755. -/
theorem bounds_15_25755 : exactInterval 15 25755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25755 : oddCount 25755 15 = 10 ∧ acceleratedOrbit 15 25755 = 46415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25755) = 3 ^ 10 * m + 46415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25755.1, data_15_25755.2]

/-- Complete interval computation for depth 15, residue 25756. -/
theorem bounds_15_25756 : exactInterval 15 25756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25756 : oddCount 25756 15 = 8 ∧ acceleratedOrbit 15 25756 = 5159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25756) = 3 ^ 8 * m + 5159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25756.1, data_15_25756.2]

/-- Complete interval computation for depth 15, residue 25757. -/
theorem bounds_15_25757 : exactInterval 15 25757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25757 : oddCount 25757 15 = 8 ∧ acceleratedOrbit 15 25757 = 5159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25757) = 3 ^ 8 * m + 5159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25757.1, data_15_25757.2]

/-- Complete interval computation for depth 15, residue 25758. -/
theorem bounds_15_25758 : exactInterval 15 25758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25758 : oddCount 25758 15 = 8 ∧ acceleratedOrbit 15 25758 = 5159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25758) = 3 ^ 8 * m + 5159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25758.1, data_15_25758.2]

/-- Complete interval computation for depth 15, residue 25759. -/
theorem bounds_15_25759 : exactInterval 15 25759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25759 : oddCount 25759 15 = 10 ∧ acceleratedOrbit 15 25759 = 46421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25759) = 3 ^ 10 * m + 46421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25759.1, data_15_25759.2]

/-- Complete interval computation for depth 15, residue 25760. -/
theorem bounds_15_25760 : exactInterval 15 25760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25760 : oddCount 25760 15 = 4 ∧ acceleratedOrbit 15 25760 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25760) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25760.1, data_15_25760.2]

/-- Complete interval computation for depth 15, residue 25761. -/
theorem bounds_15_25761 : exactInterval 15 25761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25761 : oddCount 25761 15 = 9 ∧ acceleratedOrbit 15 25761 = 15476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25761) = 3 ^ 9 * m + 15476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25761.1, data_15_25761.2]

/-- Complete interval computation for depth 15, residue 25762. -/
theorem bounds_15_25762 : exactInterval 15 25762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25762 : oddCount 25762 15 = 7 ∧ acceleratedOrbit 15 25762 = 1720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25762) = 3 ^ 7 * m + 1720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25762.1, data_15_25762.2]

/-- Complete interval computation for depth 15, residue 25763. -/
theorem bounds_15_25763 : exactInterval 15 25763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25763 : oddCount 25763 15 = 7 ∧ acceleratedOrbit 15 25763 = 1720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25763) = 3 ^ 7 * m + 1720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25763.1, data_15_25763.2]

/-- Complete interval computation for depth 15, residue 25764. -/
theorem bounds_15_25764 : exactInterval 15 25764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25764 : oddCount 25764 15 = 7 ∧ acceleratedOrbit 15 25764 = 1720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25764) = 3 ^ 7 * m + 1720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25764.1, data_15_25764.2]

/-- Complete interval computation for depth 15, residue 25765. -/
theorem bounds_15_25765 : exactInterval 15 25765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25765 : oddCount 25765 15 = 7 ∧ acceleratedOrbit 15 25765 = 1720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25765) = 3 ^ 7 * m + 1720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25765.1, data_15_25765.2]

/-- Complete interval computation for depth 15, residue 25766. -/
theorem bounds_15_25766 : exactInterval 15 25766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25766 : oddCount 25766 15 = 7 ∧ acceleratedOrbit 15 25766 = 1720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25766) = 3 ^ 7 * m + 1720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25766.1, data_15_25766.2]

/-- Complete interval computation for depth 15, residue 25767. -/
theorem bounds_15_25767 : exactInterval 15 25767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25767 : oddCount 25767 15 = 9 ∧ acceleratedOrbit 15 25767 = 15479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25767) = 3 ^ 9 * m + 15479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25767.1, data_15_25767.2]

/-- Complete interval computation for depth 15, residue 25768. -/
theorem bounds_15_25768 : exactInterval 15 25768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25768 : oddCount 25768 15 = 4 ∧ acceleratedOrbit 15 25768 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25768) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25768.1, data_15_25768.2]

/-- Complete interval computation for depth 15, residue 25769. -/
theorem bounds_15_25769 : exactInterval 15 25769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25769 : oddCount 25769 15 = 12 ∧ acceleratedOrbit 15 25769 = 417959 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25769) = 3 ^ 12 * m + 417959 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25769.1, data_15_25769.2]

/-- Complete interval computation for depth 15, residue 25770. -/
theorem bounds_15_25770 : exactInterval 15 25770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25770 : oddCount 25770 15 = 4 ∧ acceleratedOrbit 15 25770 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25770) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25770.1, data_15_25770.2]

/-- Complete interval computation for depth 15, residue 25771. -/
theorem bounds_15_25771 : exactInterval 15 25771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25771 : oddCount 25771 15 = 7 ∧ acceleratedOrbit 15 25771 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25771) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25771.1, data_15_25771.2]

/-- Complete interval computation for depth 15, residue 25772. -/
theorem bounds_15_25772 : exactInterval 15 25772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25772 : oddCount 25772 15 = 7 ∧ acceleratedOrbit 15 25772 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25772) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25772.1, data_15_25772.2]

/-- Complete interval computation for depth 15, residue 25773. -/
theorem bounds_15_25773 : exactInterval 15 25773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25773 : oddCount 25773 15 = 7 ∧ acceleratedOrbit 15 25773 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25773) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25773.1, data_15_25773.2]

/-- Complete interval computation for depth 15, residue 25774. -/
theorem bounds_15_25774 : exactInterval 15 25774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25774 : oddCount 25774 15 = 7 ∧ acceleratedOrbit 15 25774 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25774) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25774.1, data_15_25774.2]

/-- Complete interval computation for depth 15, residue 25775. -/
theorem bounds_15_25775 : exactInterval 15 25775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25775 : oddCount 25775 15 = 9 ∧ acceleratedOrbit 15 25775 = 15484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25775) = 3 ^ 9 * m + 15484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25775.1, data_15_25775.2]

/-- Complete interval computation for depth 15, residue 25776. -/
theorem bounds_15_25776 : exactInterval 15 25776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25776 : oddCount 25776 15 = 4 ∧ acceleratedOrbit 15 25776 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25776) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25776.1, data_15_25776.2]

/-- Complete interval computation for depth 15, residue 25777. -/
theorem bounds_15_25777 : exactInterval 15 25777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25777 : oddCount 25777 15 = 9 ∧ acceleratedOrbit 15 25777 = 15491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25777) = 3 ^ 9 * m + 15491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25777.1, data_15_25777.2]

/-- Complete interval computation for depth 15, residue 25778. -/
theorem bounds_15_25778 : exactInterval 15 25778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25778 : oddCount 25778 15 = 9 ∧ acceleratedOrbit 15 25778 = 15491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25778) = 3 ^ 9 * m + 15491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25778.1, data_15_25778.2]

/-- Complete interval computation for depth 15, residue 25779. -/
theorem bounds_15_25779 : exactInterval 15 25779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25779 : oddCount 25779 15 = 9 ∧ acceleratedOrbit 15 25779 = 15491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25779) = 3 ^ 9 * m + 15491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25779.1, data_15_25779.2]

/-- Complete interval computation for depth 15, residue 25780. -/
theorem bounds_15_25780 : exactInterval 15 25780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25780 : oddCount 25780 15 = 4 ∧ acceleratedOrbit 15 25780 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25780) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25780.1, data_15_25780.2]

/-- Complete interval computation for depth 15, residue 25781. -/
theorem bounds_15_25781 : exactInterval 15 25781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25781 : oddCount 25781 15 = 4 ∧ acceleratedOrbit 15 25781 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25781) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25781.1, data_15_25781.2]

/-- Complete interval computation for depth 15, residue 25782. -/
theorem bounds_15_25782 : exactInterval 15 25782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25782 : oddCount 25782 15 = 11 ∧ acceleratedOrbit 15 25782 = 139400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25782) = 3 ^ 11 * m + 139400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25782.1, data_15_25782.2]

/-- Complete interval computation for depth 15, residue 25783. -/
theorem bounds_15_25783 : exactInterval 15 25783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25783 : oddCount 25783 15 = 11 ∧ acceleratedOrbit 15 25783 = 139400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25783) = 3 ^ 11 * m + 139400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25783.1, data_15_25783.2]

/-- Complete interval computation for depth 15, residue 25784. -/
theorem bounds_15_25784 : exactInterval 15 25784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25784 : oddCount 25784 15 = 4 ∧ acceleratedOrbit 15 25784 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25784) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25784.1, data_15_25784.2]

/-- Complete interval computation for depth 15, residue 25785. -/
theorem bounds_15_25785 : exactInterval 15 25785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25785 : oddCount 25785 15 = 9 ∧ acceleratedOrbit 15 25785 = 15491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25785) = 3 ^ 9 * m + 15491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25785.1, data_15_25785.2]

/-- Complete interval computation for depth 15, residue 25786. -/
theorem bounds_15_25786 : exactInterval 15 25786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25786 : oddCount 25786 15 = 4 ∧ acceleratedOrbit 15 25786 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25786) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25786.1, data_15_25786.2]

/-- Complete interval computation for depth 15, residue 25787. -/
theorem bounds_15_25787 : exactInterval 15 25787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25787 : oddCount 25787 15 = 11 ∧ acceleratedOrbit 15 25787 = 139421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25787) = 3 ^ 11 * m + 139421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25787.1, data_15_25787.2]

end Collatz.Research.PassageAtlas.Batch0787
