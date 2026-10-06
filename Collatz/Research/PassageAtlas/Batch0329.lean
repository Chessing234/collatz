import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0329

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10747. -/
theorem bounds_15_10747 : exactInterval 15 10747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10747 : oddCount 10747 15 = 8 ∧ acceleratedOrbit 15 10747 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10747) = 3 ^ 8 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10747.1, data_15_10747.2]

/-- Complete interval computation for depth 15, residue 10748. -/
theorem bounds_15_10748 : exactInterval 15 10748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10748 : oddCount 10748 15 = 10 ∧ acceleratedOrbit 15 10748 = 19376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10748) = 3 ^ 10 * m + 19376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10748.1, data_15_10748.2]

/-- Complete interval computation for depth 15, residue 10749. -/
theorem bounds_15_10749 : exactInterval 15 10749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10749 : oddCount 10749 15 = 10 ∧ acceleratedOrbit 15 10749 = 19376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10749) = 3 ^ 10 * m + 19376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10749.1, data_15_10749.2]

/-- Complete interval computation for depth 15, residue 10750. -/
theorem bounds_15_10750 : exactInterval 15 10750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10750 : oddCount 10750 15 = 10 ∧ acceleratedOrbit 15 10750 = 19376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10750) = 3 ^ 10 * m + 19376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10750.1, data_15_10750.2]

/-- Complete interval computation for depth 15, residue 10751. -/
theorem bounds_15_10751 : exactInterval 15 10751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10751 : oddCount 10751 15 = 13 ∧ acceleratedOrbit 15 10751 = 523138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10751) = 3 ^ 13 * m + 523138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10751.1, data_15_10751.2]

/-- Complete interval computation for depth 15, residue 10752. -/
theorem bounds_15_10752 : exactInterval 15 10752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10752 : oddCount 10752 15 = 1 ∧ acceleratedOrbit 15 10752 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10752) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10752.1, data_15_10752.2]

/-- Complete interval computation for depth 15, residue 10753. -/
theorem bounds_15_10753 : exactInterval 15 10753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10753 : oddCount 10753 15 = 7 ∧ acceleratedOrbit 15 10753 = 718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10753) = 3 ^ 7 * m + 718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10753.1, data_15_10753.2]

/-- Complete interval computation for depth 15, residue 10754. -/
theorem bounds_15_10754 : exactInterval 15 10754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10754 : oddCount 10754 15 = 7 ∧ acceleratedOrbit 15 10754 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10754) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10754.1, data_15_10754.2]

/-- Complete interval computation for depth 15, residue 10755. -/
theorem bounds_15_10755 : exactInterval 15 10755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10755 : oddCount 10755 15 = 7 ∧ acceleratedOrbit 15 10755 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10755) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10755.1, data_15_10755.2]

/-- Complete interval computation for depth 15, residue 10756. -/
theorem bounds_15_10756 : exactInterval 15 10756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10756 : oddCount 10756 15 = 9 ∧ acceleratedOrbit 15 10756 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10756) = 3 ^ 9 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10756.1, data_15_10756.2]

/-- Complete interval computation for depth 15, residue 10757. -/
theorem bounds_15_10757 : exactInterval 15 10757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10757 : oddCount 10757 15 = 9 ∧ acceleratedOrbit 15 10757 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10757) = 3 ^ 9 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10757.1, data_15_10757.2]

/-- Complete interval computation for depth 15, residue 10758. -/
theorem bounds_15_10758 : exactInterval 15 10758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10758 : oddCount 10758 15 = 9 ∧ acceleratedOrbit 15 10758 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10758) = 3 ^ 9 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10758.1, data_15_10758.2]

/-- Complete interval computation for depth 15, residue 10759. -/
theorem bounds_15_10759 : exactInterval 15 10759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10759 : oddCount 10759 15 = 8 ∧ acceleratedOrbit 15 10759 = 2155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10759) = 3 ^ 8 * m + 2155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10759.1, data_15_10759.2]

/-- Complete interval computation for depth 15, residue 10760. -/
theorem bounds_15_10760 : exactInterval 15 10760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10760 : oddCount 10760 15 = 6 ∧ acceleratedOrbit 15 10760 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10760) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10760.1, data_15_10760.2]

/-- Complete interval computation for depth 15, residue 10761. -/
theorem bounds_15_10761 : exactInterval 15 10761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10761 : oddCount 10761 15 = 7 ∧ acceleratedOrbit 15 10761 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10761) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10761.1, data_15_10761.2]

/-- Complete interval computation for depth 15, residue 10762. -/
theorem bounds_15_10762 : exactInterval 15 10762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10762 : oddCount 10762 15 = 6 ∧ acceleratedOrbit 15 10762 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10762) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10762.1, data_15_10762.2]

/-- Complete interval computation for depth 15, residue 10763. -/
theorem bounds_15_10763 : exactInterval 15 10763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10763 : oddCount 10763 15 = 9 ∧ acceleratedOrbit 15 10763 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10763) = 3 ^ 9 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10763.1, data_15_10763.2]

/-- Complete interval computation for depth 15, residue 10764. -/
theorem bounds_15_10764 : exactInterval 15 10764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10764 : oddCount 10764 15 = 6 ∧ acceleratedOrbit 15 10764 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10764) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10764.1, data_15_10764.2]

/-- Complete interval computation for depth 15, residue 10765. -/
theorem bounds_15_10765 : exactInterval 15 10765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10765 : oddCount 10765 15 = 6 ∧ acceleratedOrbit 15 10765 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10765) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10765.1, data_15_10765.2]

/-- Complete interval computation for depth 15, residue 10766. -/
theorem bounds_15_10766 : exactInterval 15 10766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10766 : oddCount 10766 15 = 9 ∧ acceleratedOrbit 15 10766 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10766) = 3 ^ 9 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10766.1, data_15_10766.2]

/-- Complete interval computation for depth 15, residue 10767. -/
theorem bounds_15_10767 : exactInterval 15 10767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10767 : oddCount 10767 15 = 9 ∧ acceleratedOrbit 15 10767 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10767) = 3 ^ 9 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10767.1, data_15_10767.2]

/-- Complete interval computation for depth 15, residue 10768. -/
theorem bounds_15_10768 : exactInterval 15 10768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10768 : oddCount 10768 15 = 7 ∧ acceleratedOrbit 15 10768 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10768) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10768.1, data_15_10768.2]

/-- Complete interval computation for depth 15, residue 10769. -/
theorem bounds_15_10769 : exactInterval 15 10769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10769 : oddCount 10769 15 = 6 ∧ acceleratedOrbit 15 10769 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10769) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10769.1, data_15_10769.2]

/-- Complete interval computation for depth 15, residue 10770. -/
theorem bounds_15_10770 : exactInterval 15 10770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10770 : oddCount 10770 15 = 9 ∧ acceleratedOrbit 15 10770 = 6473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10770) = 3 ^ 9 * m + 6473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10770.1, data_15_10770.2]

/-- Complete interval computation for depth 15, residue 10771. -/
theorem bounds_15_10771 : exactInterval 15 10771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10771 : oddCount 10771 15 = 9 ∧ acceleratedOrbit 15 10771 = 6473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10771) = 3 ^ 9 * m + 6473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10771.1, data_15_10771.2]

/-- Complete interval computation for depth 15, residue 10772. -/
theorem bounds_15_10772 : exactInterval 15 10772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10772 : oddCount 10772 15 = 7 ∧ acceleratedOrbit 15 10772 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10772) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10772.1, data_15_10772.2]

/-- Complete interval computation for depth 15, residue 10773. -/
theorem bounds_15_10773 : exactInterval 15 10773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10773 : oddCount 10773 15 = 7 ∧ acceleratedOrbit 15 10773 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10773) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10773.1, data_15_10773.2]

/-- Complete interval computation for depth 15, residue 10774. -/
theorem bounds_15_10774 : exactInterval 15 10774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10774 : oddCount 10774 15 = 9 ∧ acceleratedOrbit 15 10774 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10774) = 3 ^ 9 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10774.1, data_15_10774.2]

/-- Complete interval computation for depth 15, residue 10775. -/
theorem bounds_15_10775 : exactInterval 15 10775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10775 : oddCount 10775 15 = 9 ∧ acceleratedOrbit 15 10775 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10775) = 3 ^ 9 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10775.1, data_15_10775.2]

/-- Complete interval computation for depth 15, residue 10776. -/
theorem bounds_15_10776 : exactInterval 15 10776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10776 : oddCount 10776 15 = 7 ∧ acceleratedOrbit 15 10776 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10776) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10776.1, data_15_10776.2]

/-- Complete interval computation for depth 15, residue 10777. -/
theorem bounds_15_10777 : exactInterval 15 10777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10777 : oddCount 10777 15 = 9 ∧ acceleratedOrbit 15 10777 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10777) = 3 ^ 9 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10777.1, data_15_10777.2]

/-- Complete interval computation for depth 15, residue 10778. -/
theorem bounds_15_10778 : exactInterval 15 10778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10778 : oddCount 10778 15 = 7 ∧ acceleratedOrbit 15 10778 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10778) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10778.1, data_15_10778.2]

/-- Complete interval computation for depth 15, residue 10779. -/
theorem bounds_15_10779 : exactInterval 15 10779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10779 : oddCount 10779 15 = 8 ∧ acceleratedOrbit 15 10779 = 2159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10779) = 3 ^ 8 * m + 2159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10779.1, data_15_10779.2]

end Collatz.Research.PassageAtlas.Batch0329
