import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0573

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18743. -/
theorem bounds_15_18743 : exactInterval 15 18743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18743 : oddCount 18743 15 = 9 ∧ acceleratedOrbit 15 18743 = 11260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18743) = 3 ^ 9 * m + 11260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18743.1, data_15_18743.2]

/-- Complete interval computation for depth 15, residue 18744. -/
theorem bounds_15_18744 : exactInterval 15 18744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18744 : oddCount 18744 15 = 7 ∧ acceleratedOrbit 15 18744 = 1252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18744) = 3 ^ 7 * m + 1252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18744.1, data_15_18744.2]

/-- Complete interval computation for depth 15, residue 18745. -/
theorem bounds_15_18745 : exactInterval 15 18745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18745 : oddCount 18745 15 = 8 ∧ acceleratedOrbit 15 18745 = 3754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18745) = 3 ^ 8 * m + 3754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18745.1, data_15_18745.2]

/-- Complete interval computation for depth 15, residue 18746. -/
theorem bounds_15_18746 : exactInterval 15 18746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18746 : oddCount 18746 15 = 7 ∧ acceleratedOrbit 15 18746 = 1252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18746) = 3 ^ 7 * m + 1252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18746.1, data_15_18746.2]

/-- Complete interval computation for depth 15, residue 18747. -/
theorem bounds_15_18747 : exactInterval 15 18747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18747 : oddCount 18747 15 = 7 ∧ acceleratedOrbit 15 18747 = 1252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18747) = 3 ^ 7 * m + 1252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18747.1, data_15_18747.2]

/-- Complete interval computation for depth 15, residue 18748. -/
theorem bounds_15_18748 : exactInterval 15 18748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18748 : oddCount 18748 15 = 7 ∧ acceleratedOrbit 15 18748 = 1252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18748) = 3 ^ 7 * m + 1252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18748.1, data_15_18748.2]

/-- Complete interval computation for depth 15, residue 18749. -/
theorem bounds_15_18749 : exactInterval 15 18749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18749 : oddCount 18749 15 = 7 ∧ acceleratedOrbit 15 18749 = 1252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18749) = 3 ^ 7 * m + 1252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18749.1, data_15_18749.2]

/-- Complete interval computation for depth 15, residue 18750. -/
theorem bounds_15_18750 : exactInterval 15 18750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18750 : oddCount 18750 15 = 9 ∧ acceleratedOrbit 15 18750 = 11264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18750) = 3 ^ 9 * m + 11264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18750.1, data_15_18750.2]

/-- Complete interval computation for depth 15, residue 18751. -/
theorem bounds_15_18751 : exactInterval 15 18751 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18751) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18751 : oddCount 18751 15 = 9 ∧ acceleratedOrbit 15 18751 = 11264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18751) = 3 ^ 9 * m + 11264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18751.1, data_15_18751.2]

/-- Complete interval computation for depth 15, residue 18752. -/
theorem bounds_15_18752 : exactInterval 15 18752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18752 : oddCount 18752 15 = 4 ∧ acceleratedOrbit 15 18752 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18752) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18752.1, data_15_18752.2]

/-- Complete interval computation for depth 15, residue 18753. -/
theorem bounds_15_18753 : exactInterval 15 18753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18753 : oddCount 18753 15 = 6 ∧ acceleratedOrbit 15 18753 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18753) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18753.1, data_15_18753.2]

/-- Complete interval computation for depth 15, residue 18754. -/
theorem bounds_15_18754 : exactInterval 15 18754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18754 : oddCount 18754 15 = 9 ∧ acceleratedOrbit 15 18754 = 11269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18754) = 3 ^ 9 * m + 11269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18754.1, data_15_18754.2]

/-- Complete interval computation for depth 15, residue 18755. -/
theorem bounds_15_18755 : exactInterval 15 18755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18755 : oddCount 18755 15 = 9 ∧ acceleratedOrbit 15 18755 = 11269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18755) = 3 ^ 9 * m + 11269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18755.1, data_15_18755.2]

/-- Complete interval computation for depth 15, residue 18756. -/
theorem bounds_15_18756 : exactInterval 15 18756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18756 : oddCount 18756 15 = 7 ∧ acceleratedOrbit 15 18756 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18756) = 3 ^ 7 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18756.1, data_15_18756.2]

/-- Complete interval computation for depth 15, residue 18757. -/
theorem bounds_15_18757 : exactInterval 15 18757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18757 : oddCount 18757 15 = 7 ∧ acceleratedOrbit 15 18757 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18757) = 3 ^ 7 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18757.1, data_15_18757.2]

/-- Complete interval computation for depth 15, residue 18758. -/
theorem bounds_15_18758 : exactInterval 15 18758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18758 : oddCount 18758 15 = 7 ∧ acceleratedOrbit 15 18758 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18758) = 3 ^ 7 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18758.1, data_15_18758.2]

/-- Complete interval computation for depth 15, residue 18759. -/
theorem bounds_15_18759 : exactInterval 15 18759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18759 : oddCount 18759 15 = 11 ∧ acceleratedOrbit 15 18759 = 101422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18759) = 3 ^ 11 * m + 101422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18759.1, data_15_18759.2]

/-- Complete interval computation for depth 15, residue 18760. -/
theorem bounds_15_18760 : exactInterval 15 18760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18760 : oddCount 18760 15 = 7 ∧ acceleratedOrbit 15 18760 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18760) = 3 ^ 7 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18760.1, data_15_18760.2]

/-- Complete interval computation for depth 15, residue 18761. -/
theorem bounds_15_18761 : exactInterval 15 18761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18761 : oddCount 18761 15 = 9 ∧ acceleratedOrbit 15 18761 = 11272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18761) = 3 ^ 9 * m + 11272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18761.1, data_15_18761.2]

/-- Complete interval computation for depth 15, residue 18762. -/
theorem bounds_15_18762 : exactInterval 15 18762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18762 : oddCount 18762 15 = 7 ∧ acceleratedOrbit 15 18762 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18762) = 3 ^ 7 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18762.1, data_15_18762.2]

/-- Complete interval computation for depth 15, residue 18763. -/
theorem bounds_15_18763 : exactInterval 15 18763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18763 : oddCount 18763 15 = 7 ∧ acceleratedOrbit 15 18763 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18763) = 3 ^ 7 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18763.1, data_15_18763.2]

/-- Complete interval computation for depth 15, residue 18764. -/
theorem bounds_15_18764 : exactInterval 15 18764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18764 : oddCount 18764 15 = 7 ∧ acceleratedOrbit 15 18764 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18764) = 3 ^ 7 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18764.1, data_15_18764.2]

/-- Complete interval computation for depth 15, residue 18765. -/
theorem bounds_15_18765 : exactInterval 15 18765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18765 : oddCount 18765 15 = 7 ∧ acceleratedOrbit 15 18765 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18765) = 3 ^ 7 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18765.1, data_15_18765.2]

/-- Complete interval computation for depth 15, residue 18766. -/
theorem bounds_15_18766 : exactInterval 15 18766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18766 : oddCount 18766 15 = 8 ∧ acceleratedOrbit 15 18766 = 3758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18766) = 3 ^ 8 * m + 3758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18766.1, data_15_18766.2]

/-- Complete interval computation for depth 15, residue 18767. -/
theorem bounds_15_18767 : exactInterval 15 18767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18767 : oddCount 18767 15 = 8 ∧ acceleratedOrbit 15 18767 = 3758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18767) = 3 ^ 8 * m + 3758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18767.1, data_15_18767.2]

/-- Complete interval computation for depth 15, residue 18768. -/
theorem bounds_15_18768 : exactInterval 15 18768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18768 : oddCount 18768 15 = 4 ∧ acceleratedOrbit 15 18768 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18768) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18768.1, data_15_18768.2]

/-- Complete interval computation for depth 15, residue 18769. -/
theorem bounds_15_18769 : exactInterval 15 18769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18769 : oddCount 18769 15 = 11 ∧ acceleratedOrbit 15 18769 = 101492 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18769) = 3 ^ 11 * m + 101492 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18769.1, data_15_18769.2]

/-- Complete interval computation for depth 15, residue 18770. -/
theorem bounds_15_18770 : exactInterval 15 18770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18770 : oddCount 18770 15 = 11 ∧ acceleratedOrbit 15 18770 = 101492 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18770) = 3 ^ 11 * m + 101492 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18770.1, data_15_18770.2]

/-- Complete interval computation for depth 15, residue 18771. -/
theorem bounds_15_18771 : exactInterval 15 18771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18771 : oddCount 18771 15 = 11 ∧ acceleratedOrbit 15 18771 = 101492 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18771) = 3 ^ 11 * m + 101492 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18771.1, data_15_18771.2]

/-- Complete interval computation for depth 15, residue 18772. -/
theorem bounds_15_18772 : exactInterval 15 18772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18772 : oddCount 18772 15 = 4 ∧ acceleratedOrbit 15 18772 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18772) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18772.1, data_15_18772.2]

/-- Complete interval computation for depth 15, residue 18773. -/
theorem bounds_15_18773 : exactInterval 15 18773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18773 : oddCount 18773 15 = 4 ∧ acceleratedOrbit 15 18773 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18773) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18773.1, data_15_18773.2]

/-- Complete interval computation for depth 15, residue 18774. -/
theorem bounds_15_18774 : exactInterval 15 18774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18774 : oddCount 18774 15 = 6 ∧ acceleratedOrbit 15 18774 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18774) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18774.1, data_15_18774.2]

/-- Complete interval computation for depth 15, residue 18775. -/
theorem bounds_15_18775 : exactInterval 15 18775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18775 : oddCount 18775 15 = 6 ∧ acceleratedOrbit 15 18775 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18775) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18775.1, data_15_18775.2]

end Collatz.Research.PassageAtlas.Batch0573
