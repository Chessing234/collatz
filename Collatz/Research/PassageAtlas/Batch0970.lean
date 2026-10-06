import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0970

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31752. -/
theorem bounds_15_31752 : exactInterval 15 31752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31752 : oddCount 31752 15 = 6 ∧ acceleratedOrbit 15 31752 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31752) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31752.1, data_15_31752.2]

/-- Complete interval computation for depth 15, residue 31753. -/
theorem bounds_15_31753 : exactInterval 15 31753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31753 : oddCount 31753 15 = 10 ∧ acceleratedOrbit 15 31753 = 57226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31753) = 3 ^ 10 * m + 57226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31753.1, data_15_31753.2]

/-- Complete interval computation for depth 15, residue 31754. -/
theorem bounds_15_31754 : exactInterval 15 31754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31754 : oddCount 31754 15 = 6 ∧ acceleratedOrbit 15 31754 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31754) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31754.1, data_15_31754.2]

/-- Complete interval computation for depth 15, residue 31755. -/
theorem bounds_15_31755 : exactInterval 15 31755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31755 : oddCount 31755 15 = 5 ∧ acceleratedOrbit 15 31755 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31755) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31755.1, data_15_31755.2]

/-- Complete interval computation for depth 15, residue 31756. -/
theorem bounds_15_31756 : exactInterval 15 31756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31756 : oddCount 31756 15 = 6 ∧ acceleratedOrbit 15 31756 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31756) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31756.1, data_15_31756.2]

/-- Complete interval computation for depth 15, residue 31757. -/
theorem bounds_15_31757 : exactInterval 15 31757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31757 : oddCount 31757 15 = 6 ∧ acceleratedOrbit 15 31757 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31757) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31757.1, data_15_31757.2]

/-- Complete interval computation for depth 15, residue 31758. -/
theorem bounds_15_31758 : exactInterval 15 31758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31758 : oddCount 31758 15 = 7 ∧ acceleratedOrbit 15 31758 = 2120 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31758) = 3 ^ 7 * m + 2120 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31758.1, data_15_31758.2]

/-- Complete interval computation for depth 15, residue 31759. -/
theorem bounds_15_31759 : exactInterval 15 31759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31759 : oddCount 31759 15 = 7 ∧ acceleratedOrbit 15 31759 = 2120 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31759) = 3 ^ 7 * m + 2120 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31759.1, data_15_31759.2]

/-- Complete interval computation for depth 15, residue 31760. -/
theorem bounds_15_31760 : exactInterval 15 31760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31760 : oddCount 31760 15 = 5 ∧ acceleratedOrbit 15 31760 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31760) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31760.1, data_15_31760.2]

/-- Complete interval computation for depth 15, residue 31761. -/
theorem bounds_15_31761 : exactInterval 15 31761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31761 : oddCount 31761 15 = 6 ∧ acceleratedOrbit 15 31761 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31761) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31761.1, data_15_31761.2]

/-- Complete interval computation for depth 15, residue 31762. -/
theorem bounds_15_31762 : exactInterval 15 31762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31762 : oddCount 31762 15 = 8 ∧ acceleratedOrbit 15 31762 = 6362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31762) = 3 ^ 8 * m + 6362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31762.1, data_15_31762.2]

/-- Complete interval computation for depth 15, residue 31763. -/
theorem bounds_15_31763 : exactInterval 15 31763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31763 : oddCount 31763 15 = 8 ∧ acceleratedOrbit 15 31763 = 6362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31763) = 3 ^ 8 * m + 6362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31763.1, data_15_31763.2]

/-- Complete interval computation for depth 15, residue 31764. -/
theorem bounds_15_31764 : exactInterval 15 31764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31764 : oddCount 31764 15 = 5 ∧ acceleratedOrbit 15 31764 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31764) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31764.1, data_15_31764.2]

/-- Complete interval computation for depth 15, residue 31765. -/
theorem bounds_15_31765 : exactInterval 15 31765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31765 : oddCount 31765 15 = 5 ∧ acceleratedOrbit 15 31765 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31765) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31765.1, data_15_31765.2]

/-- Complete interval computation for depth 15, residue 31766. -/
theorem bounds_15_31766 : exactInterval 15 31766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31766 : oddCount 31766 15 = 6 ∧ acceleratedOrbit 15 31766 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31766) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31766.1, data_15_31766.2]

/-- Complete interval computation for depth 15, residue 31767. -/
theorem bounds_15_31767 : exactInterval 15 31767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31767 : oddCount 31767 15 = 6 ∧ acceleratedOrbit 15 31767 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31767) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31767.1, data_15_31767.2]

/-- Complete interval computation for depth 15, residue 31768. -/
theorem bounds_15_31768 : exactInterval 15 31768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31768 : oddCount 31768 15 = 5 ∧ acceleratedOrbit 15 31768 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31768) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31768.1, data_15_31768.2]

/-- Complete interval computation for depth 15, residue 31769. -/
theorem bounds_15_31769 : exactInterval 15 31769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31769 : oddCount 31769 15 = 10 ∧ acceleratedOrbit 15 31769 = 57257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31769) = 3 ^ 10 * m + 57257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31769.1, data_15_31769.2]

/-- Complete interval computation for depth 15, residue 31770. -/
theorem bounds_15_31770 : exactInterval 15 31770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31770 : oddCount 31770 15 = 5 ∧ acceleratedOrbit 15 31770 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31770) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31770.1, data_15_31770.2]

/-- Complete interval computation for depth 15, residue 31771. -/
theorem bounds_15_31771 : exactInterval 15 31771 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31771) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31771 : oddCount 31771 15 = 9 ∧ acceleratedOrbit 15 31771 = 19085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31771) = 3 ^ 9 * m + 19085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31771.1, data_15_31771.2]

/-- Complete interval computation for depth 15, residue 31772. -/
theorem bounds_15_31772 : exactInterval 15 31772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31772 : oddCount 31772 15 = 6 ∧ acceleratedOrbit 15 31772 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31772) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31772.1, data_15_31772.2]

/-- Complete interval computation for depth 15, residue 31773. -/
theorem bounds_15_31773 : exactInterval 15 31773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31773 : oddCount 31773 15 = 6 ∧ acceleratedOrbit 15 31773 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31773) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31773.1, data_15_31773.2]

/-- Complete interval computation for depth 15, residue 31774. -/
theorem bounds_15_31774 : exactInterval 15 31774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31774 : oddCount 31774 15 = 6 ∧ acceleratedOrbit 15 31774 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31774) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31774.1, data_15_31774.2]

/-- Complete interval computation for depth 15, residue 31775. -/
theorem bounds_15_31775 : exactInterval 15 31775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31775 : oddCount 31775 15 = 10 ∧ acceleratedOrbit 15 31775 = 57262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31775) = 3 ^ 10 * m + 57262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31775.1, data_15_31775.2]

/-- Complete interval computation for depth 15, residue 31776. -/
theorem bounds_15_31776 : exactInterval 15 31776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31776 : oddCount 31776 15 = 7 ∧ acceleratedOrbit 15 31776 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31776) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31776.1, data_15_31776.2]

/-- Complete interval computation for depth 15, residue 31777. -/
theorem bounds_15_31777 : exactInterval 15 31777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31777 : oddCount 31777 15 = 9 ∧ acceleratedOrbit 15 31777 = 19091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31777) = 3 ^ 9 * m + 19091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31777.1, data_15_31777.2]

/-- Complete interval computation for depth 15, residue 31778. -/
theorem bounds_15_31778 : exactInterval 15 31778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31778 : oddCount 31778 15 = 5 ∧ acceleratedOrbit 15 31778 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31778) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31778.1, data_15_31778.2]

/-- Complete interval computation for depth 15, residue 31779. -/
theorem bounds_15_31779 : exactInterval 15 31779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31779 : oddCount 31779 15 = 5 ∧ acceleratedOrbit 15 31779 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31779) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31779.1, data_15_31779.2]

/-- Complete interval computation for depth 15, residue 31780. -/
theorem bounds_15_31780 : exactInterval 15 31780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31780 : oddCount 31780 15 = 8 ∧ acceleratedOrbit 15 31780 = 6365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31780) = 3 ^ 8 * m + 6365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31780.1, data_15_31780.2]

/-- Complete interval computation for depth 15, residue 31781. -/
theorem bounds_15_31781 : exactInterval 15 31781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31781 : oddCount 31781 15 = 8 ∧ acceleratedOrbit 15 31781 = 6365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31781) = 3 ^ 8 * m + 6365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31781.1, data_15_31781.2]

/-- Complete interval computation for depth 15, residue 31782. -/
theorem bounds_15_31782 : exactInterval 15 31782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31782 : oddCount 31782 15 = 8 ∧ acceleratedOrbit 15 31782 = 6365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31782) = 3 ^ 8 * m + 6365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31782.1, data_15_31782.2]

/-- Complete interval computation for depth 15, residue 31783. -/
theorem bounds_15_31783 : exactInterval 15 31783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31783 : oddCount 31783 15 = 8 ∧ acceleratedOrbit 15 31783 = 6365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31783) = 3 ^ 8 * m + 6365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31783.1, data_15_31783.2]

end Collatz.Research.PassageAtlas.Batch0970
