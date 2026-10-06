import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0665

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21757. -/
theorem bounds_15_21757 : exactInterval 15 21757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21757 : oddCount 21757 15 = 8 ∧ acceleratedOrbit 15 21757 = 4357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21757) = 3 ^ 8 * m + 4357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21757.1, data_15_21757.2]

/-- Complete interval computation for depth 15, residue 21758. -/
theorem bounds_15_21758 : exactInterval 15 21758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21758 : oddCount 21758 15 = 11 ∧ acceleratedOrbit 15 21758 = 117638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21758) = 3 ^ 11 * m + 117638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21758.1, data_15_21758.2]

/-- Complete interval computation for depth 15, residue 21759. -/
theorem bounds_15_21759 : exactInterval 15 21759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21759 : oddCount 21759 15 = 11 ∧ acceleratedOrbit 15 21759 = 117638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21759) = 3 ^ 11 * m + 117638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21759.1, data_15_21759.2]

/-- Complete interval computation for depth 15, residue 21760. -/
theorem bounds_15_21760 : exactInterval 15 21760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21760 : oddCount 21760 15 = 1 ∧ acceleratedOrbit 15 21760 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21760) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21760.1, data_15_21760.2]

/-- Complete interval computation for depth 15, residue 21761. -/
theorem bounds_15_21761 : exactInterval 15 21761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21761 : oddCount 21761 15 = 7 ∧ acceleratedOrbit 15 21761 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21761) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21761.1, data_15_21761.2]

/-- Complete interval computation for depth 15, residue 21762. -/
theorem bounds_15_21762 : exactInterval 15 21762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21762 : oddCount 21762 15 = 10 ∧ acceleratedOrbit 15 21762 = 39230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21762) = 3 ^ 10 * m + 39230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21762.1, data_15_21762.2]

/-- Complete interval computation for depth 15, residue 21763. -/
theorem bounds_15_21763 : exactInterval 15 21763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21763 : oddCount 21763 15 = 10 ∧ acceleratedOrbit 15 21763 = 39230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21763) = 3 ^ 10 * m + 39230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21763.1, data_15_21763.2]

/-- Complete interval computation for depth 15, residue 21764. -/
theorem bounds_15_21764 : exactInterval 15 21764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21764 : oddCount 21764 15 = 7 ∧ acceleratedOrbit 15 21764 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21764) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21764.1, data_15_21764.2]

/-- Complete interval computation for depth 15, residue 21765. -/
theorem bounds_15_21765 : exactInterval 15 21765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21765 : oddCount 21765 15 = 7 ∧ acceleratedOrbit 15 21765 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21765) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21765.1, data_15_21765.2]

/-- Complete interval computation for depth 15, residue 21766. -/
theorem bounds_15_21766 : exactInterval 15 21766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21766 : oddCount 21766 15 = 7 ∧ acceleratedOrbit 15 21766 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21766) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21766.1, data_15_21766.2]

/-- Complete interval computation for depth 15, residue 21767. -/
theorem bounds_15_21767 : exactInterval 15 21767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21767 : oddCount 21767 15 = 10 ∧ acceleratedOrbit 15 21767 = 39230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21767) = 3 ^ 10 * m + 39230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21767.1, data_15_21767.2]

/-- Complete interval computation for depth 15, residue 21768. -/
theorem bounds_15_21768 : exactInterval 15 21768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21768 : oddCount 21768 15 = 8 ∧ acceleratedOrbit 15 21768 = 4364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21768) = 3 ^ 8 * m + 4364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21768.1, data_15_21768.2]

/-- Complete interval computation for depth 15, residue 21769. -/
theorem bounds_15_21769 : exactInterval 15 21769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21769 : oddCount 21769 15 = 9 ∧ acceleratedOrbit 15 21769 = 13078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21769) = 3 ^ 9 * m + 13078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21769.1, data_15_21769.2]

/-- Complete interval computation for depth 15, residue 21770. -/
theorem bounds_15_21770 : exactInterval 15 21770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21770 : oddCount 21770 15 = 8 ∧ acceleratedOrbit 15 21770 = 4364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21770) = 3 ^ 8 * m + 4364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21770.1, data_15_21770.2]

/-- Complete interval computation for depth 15, residue 21771. -/
theorem bounds_15_21771 : exactInterval 15 21771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21771 : oddCount 21771 15 = 9 ∧ acceleratedOrbit 15 21771 = 13081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21771) = 3 ^ 9 * m + 13081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21771.1, data_15_21771.2]

/-- Complete interval computation for depth 15, residue 21772. -/
theorem bounds_15_21772 : exactInterval 15 21772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21772 : oddCount 21772 15 = 8 ∧ acceleratedOrbit 15 21772 = 4364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21772) = 3 ^ 8 * m + 4364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21772.1, data_15_21772.2]

/-- Complete interval computation for depth 15, residue 21773. -/
theorem bounds_15_21773 : exactInterval 15 21773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21773 : oddCount 21773 15 = 8 ∧ acceleratedOrbit 15 21773 = 4364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21773) = 3 ^ 8 * m + 4364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21773.1, data_15_21773.2]

/-- Complete interval computation for depth 15, residue 21774. -/
theorem bounds_15_21774 : exactInterval 15 21774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21774 : oddCount 21774 15 = 6 ∧ acceleratedOrbit 15 21774 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21774) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21774.1, data_15_21774.2]

/-- Complete interval computation for depth 15, residue 21775. -/
theorem bounds_15_21775 : exactInterval 15 21775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21775 : oddCount 21775 15 = 6 ∧ acceleratedOrbit 15 21775 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21775) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21775.1, data_15_21775.2]

/-- Complete interval computation for depth 15, residue 21776. -/
theorem bounds_15_21776 : exactInterval 15 21776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21776 : oddCount 21776 15 = 8 ∧ acceleratedOrbit 15 21776 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21776) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21776.1, data_15_21776.2]

/-- Complete interval computation for depth 15, residue 21777. -/
theorem bounds_15_21777 : exactInterval 15 21777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21777 : oddCount 21777 15 = 8 ∧ acceleratedOrbit 15 21777 = 4364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21777) = 3 ^ 8 * m + 4364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21777.1, data_15_21777.2]

/-- Complete interval computation for depth 15, residue 21778. -/
theorem bounds_15_21778 : exactInterval 15 21778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21778 : oddCount 21778 15 = 9 ∧ acceleratedOrbit 15 21778 = 13085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21778) = 3 ^ 9 * m + 13085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21778.1, data_15_21778.2]

/-- Complete interval computation for depth 15, residue 21779. -/
theorem bounds_15_21779 : exactInterval 15 21779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21779 : oddCount 21779 15 = 9 ∧ acceleratedOrbit 15 21779 = 13085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21779) = 3 ^ 9 * m + 13085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21779.1, data_15_21779.2]

/-- Complete interval computation for depth 15, residue 21780. -/
theorem bounds_15_21780 : exactInterval 15 21780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21780 : oddCount 21780 15 = 8 ∧ acceleratedOrbit 15 21780 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21780) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21780.1, data_15_21780.2]

/-- Complete interval computation for depth 15, residue 21781. -/
theorem bounds_15_21781 : exactInterval 15 21781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21781 : oddCount 21781 15 = 8 ∧ acceleratedOrbit 15 21781 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21781) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21781.1, data_15_21781.2]

/-- Complete interval computation for depth 15, residue 21782. -/
theorem bounds_15_21782 : exactInterval 15 21782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21782 : oddCount 21782 15 = 8 ∧ acceleratedOrbit 15 21782 = 4364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21782) = 3 ^ 8 * m + 4364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21782.1, data_15_21782.2]

/-- Complete interval computation for depth 15, residue 21783. -/
theorem bounds_15_21783 : exactInterval 15 21783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21783 : oddCount 21783 15 = 8 ∧ acceleratedOrbit 15 21783 = 4364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21783) = 3 ^ 8 * m + 4364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21783.1, data_15_21783.2]

/-- Complete interval computation for depth 15, residue 21784. -/
theorem bounds_15_21784 : exactInterval 15 21784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21784 : oddCount 21784 15 = 8 ∧ acceleratedOrbit 15 21784 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21784) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21784.1, data_15_21784.2]

/-- Complete interval computation for depth 15, residue 21785. -/
theorem bounds_15_21785 : exactInterval 15 21785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21785 : oddCount 21785 15 = 9 ∧ acceleratedOrbit 15 21785 = 13088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21785) = 3 ^ 9 * m + 13088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21785.1, data_15_21785.2]

/-- Complete interval computation for depth 15, residue 21786. -/
theorem bounds_15_21786 : exactInterval 15 21786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21786 : oddCount 21786 15 = 8 ∧ acceleratedOrbit 15 21786 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21786) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21786.1, data_15_21786.2]

/-- Complete interval computation for depth 15, residue 21787. -/
theorem bounds_15_21787 : exactInterval 15 21787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21787 : oddCount 21787 15 = 11 ∧ acceleratedOrbit 15 21787 = 117791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21787) = 3 ^ 11 * m + 117791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21787.1, data_15_21787.2]

/-- Complete interval computation for depth 15, residue 21788. -/
theorem bounds_15_21788 : exactInterval 15 21788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21788 : oddCount 21788 15 = 10 ∧ acceleratedOrbit 15 21788 = 39275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21788) = 3 ^ 10 * m + 39275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21788.1, data_15_21788.2]

/-- Complete interval computation for depth 15, residue 21789. -/
theorem bounds_15_21789 : exactInterval 15 21789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21789 : oddCount 21789 15 = 10 ∧ acceleratedOrbit 15 21789 = 39275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21789) = 3 ^ 10 * m + 39275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21789.1, data_15_21789.2]

end Collatz.Research.PassageAtlas.Batch0665
