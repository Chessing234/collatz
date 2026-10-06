import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0085

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2752. -/
theorem bounds_15_2752 : exactInterval 15 2752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2752 : oddCount 2752 15 = 4 ∧ acceleratedOrbit 15 2752 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2752) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2752.1, data_15_2752.2]

/-- Complete interval computation for depth 15, residue 2753. -/
theorem bounds_15_2753 : exactInterval 15 2753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2753 : oddCount 2753 15 = 6 ∧ acceleratedOrbit 15 2753 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2753) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2753.1, data_15_2753.2]

/-- Complete interval computation for depth 15, residue 2754. -/
theorem bounds_15_2754 : exactInterval 15 2754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2754 : oddCount 2754 15 = 8 ∧ acceleratedOrbit 15 2754 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2754) = 3 ^ 8 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2754.1, data_15_2754.2]

/-- Complete interval computation for depth 15, residue 2755. -/
theorem bounds_15_2755 : exactInterval 15 2755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2755 : oddCount 2755 15 = 8 ∧ acceleratedOrbit 15 2755 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2755) = 3 ^ 8 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2755.1, data_15_2755.2]

/-- Complete interval computation for depth 15, residue 2756. -/
theorem bounds_15_2756 : exactInterval 15 2756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2756 : oddCount 2756 15 = 7 ∧ acceleratedOrbit 15 2756 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2756) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2756.1, data_15_2756.2]

/-- Complete interval computation for depth 15, residue 2757. -/
theorem bounds_15_2757 : exactInterval 15 2757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2757 : oddCount 2757 15 = 7 ∧ acceleratedOrbit 15 2757 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2757) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2757.1, data_15_2757.2]

/-- Complete interval computation for depth 15, residue 2758. -/
theorem bounds_15_2758 : exactInterval 15 2758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2758 : oddCount 2758 15 = 7 ∧ acceleratedOrbit 15 2758 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2758) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2758.1, data_15_2758.2]

/-- Complete interval computation for depth 15, residue 2759. -/
theorem bounds_15_2759 : exactInterval 15 2759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2759 : oddCount 2759 15 = 9 ∧ acceleratedOrbit 15 2759 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2759) = 3 ^ 9 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2759.1, data_15_2759.2]

/-- Complete interval computation for depth 15, residue 2760. -/
theorem bounds_15_2760 : exactInterval 15 2760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2760 : oddCount 2760 15 = 7 ∧ acceleratedOrbit 15 2760 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2760) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2760.1, data_15_2760.2]

/-- Complete interval computation for depth 15, residue 2761. -/
theorem bounds_15_2761 : exactInterval 15 2761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2761 : oddCount 2761 15 = 6 ∧ acceleratedOrbit 15 2761 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2761) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2761.1, data_15_2761.2]

/-- Complete interval computation for depth 15, residue 2762. -/
theorem bounds_15_2762 : exactInterval 15 2762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2762 : oddCount 2762 15 = 7 ∧ acceleratedOrbit 15 2762 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2762) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2762.1, data_15_2762.2]

/-- Complete interval computation for depth 15, residue 2763. -/
theorem bounds_15_2763 : exactInterval 15 2763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2763 : oddCount 2763 15 = 9 ∧ acceleratedOrbit 15 2763 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2763) = 3 ^ 9 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2763.1, data_15_2763.2]

/-- Complete interval computation for depth 15, residue 2764. -/
theorem bounds_15_2764 : exactInterval 15 2764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2764 : oddCount 2764 15 = 7 ∧ acceleratedOrbit 15 2764 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2764) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2764.1, data_15_2764.2]

/-- Complete interval computation for depth 15, residue 2765. -/
theorem bounds_15_2765 : exactInterval 15 2765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2765 : oddCount 2765 15 = 7 ∧ acceleratedOrbit 15 2765 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2765) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2765.1, data_15_2765.2]

/-- Complete interval computation for depth 15, residue 2766. -/
theorem bounds_15_2766 : exactInterval 15 2766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2766 : oddCount 2766 15 = 9 ∧ acceleratedOrbit 15 2766 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2766) = 3 ^ 9 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2766.1, data_15_2766.2]

/-- Complete interval computation for depth 15, residue 2767. -/
theorem bounds_15_2767 : exactInterval 15 2767 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2767) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2767 : oddCount 2767 15 = 9 ∧ acceleratedOrbit 15 2767 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2767) = 3 ^ 9 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2767.1, data_15_2767.2]

/-- Complete interval computation for depth 15, residue 2768. -/
theorem bounds_15_2768 : exactInterval 15 2768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2768 : oddCount 2768 15 = 4 ∧ acceleratedOrbit 15 2768 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2768) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2768.1, data_15_2768.2]

/-- Complete interval computation for depth 15, residue 2769. -/
theorem bounds_15_2769 : exactInterval 15 2769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2769 : oddCount 2769 15 = 8 ∧ acceleratedOrbit 15 2769 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2769) = 3 ^ 8 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2769.1, data_15_2769.2]

/-- Complete interval computation for depth 15, residue 2770. -/
theorem bounds_15_2770 : exactInterval 15 2770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2770 : oddCount 2770 15 = 8 ∧ acceleratedOrbit 15 2770 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2770) = 3 ^ 8 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2770.1, data_15_2770.2]

/-- Complete interval computation for depth 15, residue 2771. -/
theorem bounds_15_2771 : exactInterval 15 2771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2771 : oddCount 2771 15 = 8 ∧ acceleratedOrbit 15 2771 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2771) = 3 ^ 8 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2771.1, data_15_2771.2]

/-- Complete interval computation for depth 15, residue 2772. -/
theorem bounds_15_2772 : exactInterval 15 2772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2772 : oddCount 2772 15 = 4 ∧ acceleratedOrbit 15 2772 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2772) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2772.1, data_15_2772.2]

/-- Complete interval computation for depth 15, residue 2773. -/
theorem bounds_15_2773 : exactInterval 15 2773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2773 : oddCount 2773 15 = 4 ∧ acceleratedOrbit 15 2773 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2773) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2773.1, data_15_2773.2]

/-- Complete interval computation for depth 15, residue 2774. -/
theorem bounds_15_2774 : exactInterval 15 2774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2774 : oddCount 2774 15 = 8 ∧ acceleratedOrbit 15 2774 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2774) = 3 ^ 8 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2774.1, data_15_2774.2]

/-- Complete interval computation for depth 15, residue 2775. -/
theorem bounds_15_2775 : exactInterval 15 2775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2775 : oddCount 2775 15 = 8 ∧ acceleratedOrbit 15 2775 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2775) = 3 ^ 8 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2775.1, data_15_2775.2]

/-- Complete interval computation for depth 15, residue 2776. -/
theorem bounds_15_2776 : exactInterval 15 2776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2776 : oddCount 2776 15 = 6 ∧ acceleratedOrbit 15 2776 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2776) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2776.1, data_15_2776.2]

/-- Complete interval computation for depth 15, residue 2777. -/
theorem bounds_15_2777 : exactInterval 15 2777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2777 : oddCount 2777 15 = 7 ∧ acceleratedOrbit 15 2777 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2777) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2777.1, data_15_2777.2]

/-- Complete interval computation for depth 15, residue 2778. -/
theorem bounds_15_2778 : exactInterval 15 2778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2778 : oddCount 2778 15 = 6 ∧ acceleratedOrbit 15 2778 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2778) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2778.1, data_15_2778.2]

/-- Complete interval computation for depth 15, residue 2779. -/
theorem bounds_15_2779 : exactInterval 15 2779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2779 : oddCount 2779 15 = 10 ∧ acceleratedOrbit 15 2779 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2779) = 3 ^ 10 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2779.1, data_15_2779.2]

/-- Complete interval computation for depth 15, residue 2780. -/
theorem bounds_15_2780 : exactInterval 15 2780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2780 : oddCount 2780 15 = 6 ∧ acceleratedOrbit 15 2780 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2780) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2780.1, data_15_2780.2]

/-- Complete interval computation for depth 15, residue 2781. -/
theorem bounds_15_2781 : exactInterval 15 2781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2781 : oddCount 2781 15 = 6 ∧ acceleratedOrbit 15 2781 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2781) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2781.1, data_15_2781.2]

/-- Complete interval computation for depth 15, residue 2782. -/
theorem bounds_15_2782 : exactInterval 15 2782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2782 : oddCount 2782 15 = 10 ∧ acceleratedOrbit 15 2782 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2782) = 3 ^ 10 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2782.1, data_15_2782.2]

/-- Complete interval computation for depth 15, residue 2783. -/
theorem bounds_15_2783 : exactInterval 15 2783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2783 : oddCount 2783 15 = 10 ∧ acceleratedOrbit 15 2783 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2783) = 3 ^ 10 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2783.1, data_15_2783.2]

/-- Complete interval computation for depth 15, residue 2784. -/
theorem bounds_15_2784 : exactInterval 15 2784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2784 : oddCount 2784 15 = 4 ∧ acceleratedOrbit 15 2784 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2784) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2784.1, data_15_2784.2]

end Collatz.Research.PassageAtlas.Batch0085
