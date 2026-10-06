import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0268

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8749. -/
theorem bounds_15_8749 : exactInterval 15 8749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8749 : oddCount 8749 15 = 9 ∧ acceleratedOrbit 15 8749 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8749) = 3 ^ 9 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8749.1, data_15_8749.2]

/-- Complete interval computation for depth 15, residue 8750. -/
theorem bounds_15_8750 : exactInterval 15 8750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8750 : oddCount 8750 15 = 9 ∧ acceleratedOrbit 15 8750 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8750) = 3 ^ 9 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8750.1, data_15_8750.2]

/-- Complete interval computation for depth 15, residue 8751. -/
theorem bounds_15_8751 : exactInterval 15 8751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8751 : oddCount 8751 15 = 11 ∧ acceleratedOrbit 15 8751 = 47317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8751) = 3 ^ 11 * m + 47317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8751.1, data_15_8751.2]

/-- Complete interval computation for depth 15, residue 8752. -/
theorem bounds_15_8752 : exactInterval 15 8752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8752 : oddCount 8752 15 = 4 ∧ acceleratedOrbit 15 8752 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8752) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8752.1, data_15_8752.2]

/-- Complete interval computation for depth 15, residue 8753. -/
theorem bounds_15_8753 : exactInterval 15 8753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8753 : oddCount 8753 15 = 9 ∧ acceleratedOrbit 15 8753 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8753) = 3 ^ 9 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8753.1, data_15_8753.2]

/-- Complete interval computation for depth 15, residue 8754. -/
theorem bounds_15_8754 : exactInterval 15 8754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8754 : oddCount 8754 15 = 9 ∧ acceleratedOrbit 15 8754 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8754) = 3 ^ 9 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8754.1, data_15_8754.2]

/-- Complete interval computation for depth 15, residue 8755. -/
theorem bounds_15_8755 : exactInterval 15 8755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8755 : oddCount 8755 15 = 9 ∧ acceleratedOrbit 15 8755 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8755) = 3 ^ 9 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8755.1, data_15_8755.2]

/-- Complete interval computation for depth 15, residue 8756. -/
theorem bounds_15_8756 : exactInterval 15 8756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8756 : oddCount 8756 15 = 4 ∧ acceleratedOrbit 15 8756 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8756) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8756.1, data_15_8756.2]

/-- Complete interval computation for depth 15, residue 8757. -/
theorem bounds_15_8757 : exactInterval 15 8757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8757 : oddCount 8757 15 = 4 ∧ acceleratedOrbit 15 8757 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8757) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8757.1, data_15_8757.2]

/-- Complete interval computation for depth 15, residue 8758. -/
theorem bounds_15_8758 : exactInterval 15 8758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8758 : oddCount 8758 15 = 10 ∧ acceleratedOrbit 15 8758 = 15788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8758) = 3 ^ 10 * m + 15788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8758.1, data_15_8758.2]

/-- Complete interval computation for depth 15, residue 8759. -/
theorem bounds_15_8759 : exactInterval 15 8759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8759 : oddCount 8759 15 = 10 ∧ acceleratedOrbit 15 8759 = 15788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8759) = 3 ^ 10 * m + 15788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8759.1, data_15_8759.2]

/-- Complete interval computation for depth 15, residue 8760. -/
theorem bounds_15_8760 : exactInterval 15 8760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8760 : oddCount 8760 15 = 8 ∧ acceleratedOrbit 15 8760 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8760) = 3 ^ 8 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8760.1, data_15_8760.2]

/-- Complete interval computation for depth 15, residue 8761. -/
theorem bounds_15_8761 : exactInterval 15 8761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8761 : oddCount 8761 15 = 11 ∧ acceleratedOrbit 15 8761 = 47384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8761) = 3 ^ 11 * m + 47384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8761.1, data_15_8761.2]

/-- Complete interval computation for depth 15, residue 8762. -/
theorem bounds_15_8762 : exactInterval 15 8762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8762 : oddCount 8762 15 = 8 ∧ acceleratedOrbit 15 8762 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8762) = 3 ^ 8 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8762.1, data_15_8762.2]

/-- Complete interval computation for depth 15, residue 8763. -/
theorem bounds_15_8763 : exactInterval 15 8763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8763 : oddCount 8763 15 = 5 ∧ acceleratedOrbit 15 8763 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8763) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8763.1, data_15_8763.2]

/-- Complete interval computation for depth 15, residue 8764. -/
theorem bounds_15_8764 : exactInterval 15 8764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8764 : oddCount 8764 15 = 8 ∧ acceleratedOrbit 15 8764 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8764) = 3 ^ 8 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8764.1, data_15_8764.2]

/-- Complete interval computation for depth 15, residue 8765. -/
theorem bounds_15_8765 : exactInterval 15 8765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8765 : oddCount 8765 15 = 8 ∧ acceleratedOrbit 15 8765 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8765) = 3 ^ 8 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8765.1, data_15_8765.2]

/-- Complete interval computation for depth 15, residue 8766. -/
theorem bounds_15_8766 : exactInterval 15 8766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8766 : oddCount 8766 15 = 8 ∧ acceleratedOrbit 15 8766 = 1756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8766) = 3 ^ 8 * m + 1756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8766.1, data_15_8766.2]

/-- Complete interval computation for depth 15, residue 8767. -/
theorem bounds_15_8767 : exactInterval 15 8767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8767 : oddCount 8767 15 = 8 ∧ acceleratedOrbit 15 8767 = 1756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8767) = 3 ^ 8 * m + 1756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8767.1, data_15_8767.2]

/-- Complete interval computation for depth 15, residue 8768. -/
theorem bounds_15_8768 : exactInterval 15 8768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8768 : oddCount 8768 15 = 7 ∧ acceleratedOrbit 15 8768 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8768) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8768.1, data_15_8768.2]

/-- Complete interval computation for depth 15, residue 8769. -/
theorem bounds_15_8769 : exactInterval 15 8769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8769 : oddCount 8769 15 = 7 ∧ acceleratedOrbit 15 8769 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8769) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8769.1, data_15_8769.2]

/-- Complete interval computation for depth 15, residue 8770. -/
theorem bounds_15_8770 : exactInterval 15 8770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8770 : oddCount 8770 15 = 7 ∧ acceleratedOrbit 15 8770 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8770) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8770.1, data_15_8770.2]

/-- Complete interval computation for depth 15, residue 8771. -/
theorem bounds_15_8771 : exactInterval 15 8771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8771 : oddCount 8771 15 = 7 ∧ acceleratedOrbit 15 8771 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8771) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8771.1, data_15_8771.2]

/-- Complete interval computation for depth 15, residue 8772. -/
theorem bounds_15_8772 : exactInterval 15 8772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8772 : oddCount 8772 15 = 7 ∧ acceleratedOrbit 15 8772 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8772) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8772.1, data_15_8772.2]

/-- Complete interval computation for depth 15, residue 8773. -/
theorem bounds_15_8773 : exactInterval 15 8773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8773 : oddCount 8773 15 = 7 ∧ acceleratedOrbit 15 8773 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8773) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8773.1, data_15_8773.2]

/-- Complete interval computation for depth 15, residue 8774. -/
theorem bounds_15_8774 : exactInterval 15 8774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8774 : oddCount 8774 15 = 7 ∧ acceleratedOrbit 15 8774 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8774) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8774.1, data_15_8774.2]

/-- Complete interval computation for depth 15, residue 8775. -/
theorem bounds_15_8775 : exactInterval 15 8775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8775 : oddCount 8775 15 = 7 ∧ acceleratedOrbit 15 8775 = 586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8775) = 3 ^ 7 * m + 586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8775.1, data_15_8775.2]

/-- Complete interval computation for depth 15, residue 8776. -/
theorem bounds_15_8776 : exactInterval 15 8776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8776 : oddCount 8776 15 = 7 ∧ acceleratedOrbit 15 8776 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8776) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8776.1, data_15_8776.2]

/-- Complete interval computation for depth 15, residue 8777. -/
theorem bounds_15_8777 : exactInterval 15 8777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8777 : oddCount 8777 15 = 7 ∧ acceleratedOrbit 15 8777 = 586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8777) = 3 ^ 7 * m + 586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8777.1, data_15_8777.2]

/-- Complete interval computation for depth 15, residue 8778. -/
theorem bounds_15_8778 : exactInterval 15 8778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8778 : oddCount 8778 15 = 7 ∧ acceleratedOrbit 15 8778 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8778) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8778.1, data_15_8778.2]

/-- Complete interval computation for depth 15, residue 8779. -/
theorem bounds_15_8779 : exactInterval 15 8779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8779 : oddCount 8779 15 = 7 ∧ acceleratedOrbit 15 8779 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8779) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8779.1, data_15_8779.2]

/-- Complete interval computation for depth 15, residue 8780. -/
theorem bounds_15_8780 : exactInterval 15 8780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8780 : oddCount 8780 15 = 7 ∧ acceleratedOrbit 15 8780 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8780) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8780.1, data_15_8780.2]

end Collatz.Research.PassageAtlas.Batch0268
