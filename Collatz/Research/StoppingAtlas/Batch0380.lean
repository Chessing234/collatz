import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0380

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2749. -/
theorem bounds_12_2749 : exactInterval 12 2749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2749 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2749) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2749 : oddCount 2749 12 = 6 ∧ acceleratedOrbit 12 2749 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2749 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2749) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2749.1, data_12_2749.2]

/-- Complete interval computation for depth 12, residue 2750. -/
theorem bounds_12_2750 : exactInterval 12 2750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2750 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2750) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2750 : oddCount 2750 12 = 6 ∧ acceleratedOrbit 12 2750 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2750 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2750) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2750.1, data_12_2750.2]

/-- Complete interval computation for depth 12, residue 2751. -/
theorem bounds_12_2751 : exactInterval 12 2751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2751 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2751) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2751 : oddCount 2751 12 = 9 ∧ acceleratedOrbit 12 2751 = 13225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2751 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2751) = 3 ^ 9 * m + 13225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2751.1, data_12_2751.2]

/-- Complete interval computation for depth 12, residue 2752. -/
theorem bounds_12_2752 : exactInterval 12 2752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2752 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2752) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2752 : oddCount 2752 12 = 4 ∧ acceleratedOrbit 12 2752 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2752 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2752) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2752.1, data_12_2752.2]

/-- Complete interval computation for depth 12, residue 2753. -/
theorem bounds_12_2753 : exactInterval 12 2753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2753 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2753) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2753 : oddCount 2753 12 = 5 ∧ acceleratedOrbit 12 2753 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2753 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2753) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2753.1, data_12_2753.2]

/-- Complete interval computation for depth 12, residue 2754. -/
theorem bounds_12_2754 : exactInterval 12 2754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2754 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2754) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2754 : oddCount 2754 12 = 6 ∧ acceleratedOrbit 12 2754 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2754 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2754) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2754.1, data_12_2754.2]

/-- Complete interval computation for depth 12, residue 2755. -/
theorem bounds_12_2755 : exactInterval 12 2755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2755 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2755) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2755 : oddCount 2755 12 = 6 ∧ acceleratedOrbit 12 2755 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2755 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2755) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2755.1, data_12_2755.2]

/-- Complete interval computation for depth 12, residue 2756. -/
theorem bounds_12_2756 : exactInterval 12 2756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2756 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2756) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2756 : oddCount 2756 12 = 4 ∧ acceleratedOrbit 12 2756 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2756 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2756) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2756.1, data_12_2756.2]

/-- Complete interval computation for depth 12, residue 2757. -/
theorem bounds_12_2757 : exactInterval 12 2757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2757 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2757) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2757 : oddCount 2757 12 = 4 ∧ acceleratedOrbit 12 2757 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2757 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2757) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2757.1, data_12_2757.2]

/-- Complete interval computation for depth 12, residue 2758. -/
theorem bounds_12_2758 : exactInterval 12 2758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2758 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2758) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2758 : oddCount 2758 12 = 4 ∧ acceleratedOrbit 12 2758 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2758 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2758) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2758.1, data_12_2758.2]

/-- Complete interval computation for depth 12, residue 2759. -/
theorem bounds_12_2759 : exactInterval 12 2759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2759 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2759) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2759 : oddCount 2759 12 = 7 ∧ acceleratedOrbit 12 2759 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2759 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2759) = 3 ^ 7 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2759.1, data_12_2759.2]

/-- Complete interval computation for depth 12, residue 2760. -/
theorem bounds_12_2760 : exactInterval 12 2760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2760 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2760) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2760 : oddCount 2760 12 = 4 ∧ acceleratedOrbit 12 2760 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2760 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2760) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2760.1, data_12_2760.2]

/-- Complete interval computation for depth 12, residue 2761. -/
theorem bounds_12_2761 : exactInterval 12 2761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2761 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2761) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2761 : oddCount 2761 12 = 5 ∧ acceleratedOrbit 12 2761 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2761 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2761) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2761.1, data_12_2761.2]

/-- Complete interval computation for depth 12, residue 2762. -/
theorem bounds_12_2762 : exactInterval 12 2762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2762 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2762) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2762 : oddCount 2762 12 = 4 ∧ acceleratedOrbit 12 2762 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2762 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2762) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2762.1, data_12_2762.2]

/-- Complete interval computation for depth 12, residue 2763. -/
theorem bounds_12_2763 : exactInterval 12 2763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2763 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2763) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2763 : oddCount 2763 12 = 7 ∧ acceleratedOrbit 12 2763 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2763 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2763) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2763.1, data_12_2763.2]

end Collatz.Research.StoppingAtlas.Batch0380
