import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0726

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23756. -/
theorem bounds_15_23756 : exactInterval 15 23756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23756 : oddCount 23756 15 = 6 ∧ acceleratedOrbit 15 23756 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23756) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23756.1, data_15_23756.2]

/-- Complete interval computation for depth 15, residue 23757. -/
theorem bounds_15_23757 : exactInterval 15 23757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23757 : oddCount 23757 15 = 6 ∧ acceleratedOrbit 15 23757 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23757) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23757.1, data_15_23757.2]

/-- Complete interval computation for depth 15, residue 23758. -/
theorem bounds_15_23758 : exactInterval 15 23758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23758 : oddCount 23758 15 = 9 ∧ acceleratedOrbit 15 23758 = 14273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23758) = 3 ^ 9 * m + 14273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23758.1, data_15_23758.2]

/-- Complete interval computation for depth 15, residue 23759. -/
theorem bounds_15_23759 : exactInterval 15 23759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23759 : oddCount 23759 15 = 9 ∧ acceleratedOrbit 15 23759 = 14273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23759) = 3 ^ 9 * m + 14273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23759.1, data_15_23759.2]

/-- Complete interval computation for depth 15, residue 23760. -/
theorem bounds_15_23760 : exactInterval 15 23760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23760 : oddCount 23760 15 = 4 ∧ acceleratedOrbit 15 23760 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23760) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23760.1, data_15_23760.2]

/-- Complete interval computation for depth 15, residue 23761. -/
theorem bounds_15_23761 : exactInterval 15 23761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23761 : oddCount 23761 15 = 9 ∧ acceleratedOrbit 15 23761 = 14276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23761) = 3 ^ 9 * m + 14276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23761.1, data_15_23761.2]

/-- Complete interval computation for depth 15, residue 23762. -/
theorem bounds_15_23762 : exactInterval 15 23762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23762 : oddCount 23762 15 = 9 ∧ acceleratedOrbit 15 23762 = 14276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23762) = 3 ^ 9 * m + 14276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23762.1, data_15_23762.2]

/-- Complete interval computation for depth 15, residue 23763. -/
theorem bounds_15_23763 : exactInterval 15 23763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23763 : oddCount 23763 15 = 9 ∧ acceleratedOrbit 15 23763 = 14276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23763) = 3 ^ 9 * m + 14276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23763.1, data_15_23763.2]

/-- Complete interval computation for depth 15, residue 23764. -/
theorem bounds_15_23764 : exactInterval 15 23764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23764 : oddCount 23764 15 = 4 ∧ acceleratedOrbit 15 23764 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23764) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23764.1, data_15_23764.2]

/-- Complete interval computation for depth 15, residue 23765. -/
theorem bounds_15_23765 : exactInterval 15 23765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23765 : oddCount 23765 15 = 4 ∧ acceleratedOrbit 15 23765 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23765) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23765.1, data_15_23765.2]

/-- Complete interval computation for depth 15, residue 23766. -/
theorem bounds_15_23766 : exactInterval 15 23766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23766 : oddCount 23766 15 = 8 ∧ acceleratedOrbit 15 23766 = 4760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23766) = 3 ^ 8 * m + 4760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23766.1, data_15_23766.2]

/-- Complete interval computation for depth 15, residue 23767. -/
theorem bounds_15_23767 : exactInterval 15 23767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23767 : oddCount 23767 15 = 8 ∧ acceleratedOrbit 15 23767 = 4760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23767) = 3 ^ 8 * m + 4760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23767.1, data_15_23767.2]

/-- Complete interval computation for depth 15, residue 23768. -/
theorem bounds_15_23768 : exactInterval 15 23768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23768 : oddCount 23768 15 = 6 ∧ acceleratedOrbit 15 23768 = 529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23768) = 3 ^ 6 * m + 529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23768.1, data_15_23768.2]

/-- Complete interval computation for depth 15, residue 23769. -/
theorem bounds_15_23769 : exactInterval 15 23769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23769 : oddCount 23769 15 = 6 ∧ acceleratedOrbit 15 23769 = 529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23769) = 3 ^ 6 * m + 529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23769.1, data_15_23769.2]

/-- Complete interval computation for depth 15, residue 23770. -/
theorem bounds_15_23770 : exactInterval 15 23770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23770 : oddCount 23770 15 = 6 ∧ acceleratedOrbit 15 23770 = 529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23770) = 3 ^ 6 * m + 529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23770.1, data_15_23770.2]

/-- Complete interval computation for depth 15, residue 23771. -/
theorem bounds_15_23771 : exactInterval 15 23771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23771 : oddCount 23771 15 = 9 ∧ acceleratedOrbit 15 23771 = 14282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23771) = 3 ^ 9 * m + 14282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23771.1, data_15_23771.2]

/-- Complete interval computation for depth 15, residue 23772. -/
theorem bounds_15_23772 : exactInterval 15 23772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23772 : oddCount 23772 15 = 6 ∧ acceleratedOrbit 15 23772 = 529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23772) = 3 ^ 6 * m + 529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23772.1, data_15_23772.2]

/-- Complete interval computation for depth 15, residue 23773. -/
theorem bounds_15_23773 : exactInterval 15 23773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23773 : oddCount 23773 15 = 6 ∧ acceleratedOrbit 15 23773 = 529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23773) = 3 ^ 6 * m + 529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23773.1, data_15_23773.2]

/-- Complete interval computation for depth 15, residue 23774. -/
theorem bounds_15_23774 : exactInterval 15 23774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23774 : oddCount 23774 15 = 10 ∧ acceleratedOrbit 15 23774 = 42848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23774) = 3 ^ 10 * m + 42848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23774.1, data_15_23774.2]

/-- Complete interval computation for depth 15, residue 23775. -/
theorem bounds_15_23775 : exactInterval 15 23775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23775 : oddCount 23775 15 = 10 ∧ acceleratedOrbit 15 23775 = 42848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23775) = 3 ^ 10 * m + 42848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23775.1, data_15_23775.2]

/-- Complete interval computation for depth 15, residue 23776. -/
theorem bounds_15_23776 : exactInterval 15 23776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23776 : oddCount 23776 15 = 8 ∧ acceleratedOrbit 15 23776 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23776) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23776.1, data_15_23776.2]

/-- Complete interval computation for depth 15, residue 23777. -/
theorem bounds_15_23777 : exactInterval 15 23777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23777 : oddCount 23777 15 = 9 ∧ acceleratedOrbit 15 23777 = 14284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23777) = 3 ^ 9 * m + 14284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23777.1, data_15_23777.2]

/-- Complete interval computation for depth 15, residue 23778. -/
theorem bounds_15_23778 : exactInterval 15 23778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23778 : oddCount 23778 15 = 4 ∧ acceleratedOrbit 15 23778 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23778) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23778.1, data_15_23778.2]

/-- Complete interval computation for depth 15, residue 23779. -/
theorem bounds_15_23779 : exactInterval 15 23779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23779 : oddCount 23779 15 = 4 ∧ acceleratedOrbit 15 23779 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23779) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23779.1, data_15_23779.2]

/-- Complete interval computation for depth 15, residue 23780. -/
theorem bounds_15_23780 : exactInterval 15 23780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23780 : oddCount 23780 15 = 7 ∧ acceleratedOrbit 15 23780 = 1588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23780) = 3 ^ 7 * m + 1588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23780.1, data_15_23780.2]

/-- Complete interval computation for depth 15, residue 23781. -/
theorem bounds_15_23781 : exactInterval 15 23781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23781 : oddCount 23781 15 = 7 ∧ acceleratedOrbit 15 23781 = 1588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23781) = 3 ^ 7 * m + 1588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23781.1, data_15_23781.2]

/-- Complete interval computation for depth 15, residue 23782. -/
theorem bounds_15_23782 : exactInterval 15 23782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23782 : oddCount 23782 15 = 7 ∧ acceleratedOrbit 15 23782 = 1588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23782) = 3 ^ 7 * m + 1588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23782.1, data_15_23782.2]

/-- Complete interval computation for depth 15, residue 23783. -/
theorem bounds_15_23783 : exactInterval 15 23783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23783 : oddCount 23783 15 = 9 ∧ acceleratedOrbit 15 23783 = 14287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23783) = 3 ^ 9 * m + 14287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23783.1, data_15_23783.2]

/-- Complete interval computation for depth 15, residue 23784. -/
theorem bounds_15_23784 : exactInterval 15 23784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23784 : oddCount 23784 15 = 8 ∧ acceleratedOrbit 15 23784 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23784) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23784.1, data_15_23784.2]

/-- Complete interval computation for depth 15, residue 23785. -/
theorem bounds_15_23785 : exactInterval 15 23785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23785 : oddCount 23785 15 = 8 ∧ acceleratedOrbit 15 23785 = 4763 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23785) = 3 ^ 8 * m + 4763 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23785.1, data_15_23785.2]

/-- Complete interval computation for depth 15, residue 23786. -/
theorem bounds_15_23786 : exactInterval 15 23786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23786 : oddCount 23786 15 = 8 ∧ acceleratedOrbit 15 23786 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23786) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23786.1, data_15_23786.2]

/-- Complete interval computation for depth 15, residue 23787. -/
theorem bounds_15_23787 : exactInterval 15 23787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23787 : oddCount 23787 15 = 10 ∧ acceleratedOrbit 15 23787 = 42869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23787) = 3 ^ 10 * m + 42869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23787.1, data_15_23787.2]

/-- Complete interval computation for depth 15, residue 23788. -/
theorem bounds_15_23788 : exactInterval 15 23788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23788 : oddCount 23788 15 = 6 ∧ acceleratedOrbit 15 23788 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23788) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23788.1, data_15_23788.2]

end Collatz.Research.PassageAtlas.Batch0726
