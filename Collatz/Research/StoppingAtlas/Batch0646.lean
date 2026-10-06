import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0646

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2739. -/
theorem bounds_13_2739 : exactInterval 13 2739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2739 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2739) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2739 : oddCount 2739 13 = 6 ∧ acceleratedOrbit 13 2739 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2739 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2739) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2739.1, data_13_2739.2]

/-- Complete interval computation for depth 13, residue 2740. -/
theorem bounds_13_2740 : exactInterval 13 2740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2740 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2740) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2740 : oddCount 2740 13 = 5 ∧ acceleratedOrbit 13 2740 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2740 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2740) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2740.1, data_13_2740.2]

/-- Complete interval computation for depth 13, residue 2741. -/
theorem bounds_13_2741 : exactInterval 13 2741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2741 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2741) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2741 : oddCount 2741 13 = 5 ∧ acceleratedOrbit 13 2741 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2741 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2741) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2741.1, data_13_2741.2]

/-- Complete interval computation for depth 13, residue 2742. -/
theorem bounds_13_2742 : exactInterval 13 2742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2742 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2742) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2742 : oddCount 2742 13 = 7 ∧ acceleratedOrbit 13 2742 = 733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2742 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2742) = 3 ^ 7 * m + 733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2742.1, data_13_2742.2]

/-- Complete interval computation for depth 13, residue 2743. -/
theorem bounds_13_2743 : exactInterval 13 2743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2743 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2743) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2743 : oddCount 2743 13 = 7 ∧ acceleratedOrbit 13 2743 = 733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2743 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2743) = 3 ^ 7 * m + 733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2743.1, data_13_2743.2]

/-- Complete interval computation for depth 13, residue 2744. -/
theorem bounds_13_2744 : exactInterval 13 2744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2744 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2744) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2744 : oddCount 2744 13 = 5 ∧ acceleratedOrbit 13 2744 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2744 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2744) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2744.1, data_13_2744.2]

/-- Complete interval computation for depth 13, residue 2745. -/
theorem bounds_13_2745 : exactInterval 13 2745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2745 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2745) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2745 : oddCount 2745 13 = 6 ∧ acceleratedOrbit 13 2745 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2745 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2745) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2745.1, data_13_2745.2]

/-- Complete interval computation for depth 13, residue 2746. -/
theorem bounds_13_2746 : exactInterval 13 2746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2746 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2746) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2746 : oddCount 2746 13 = 5 ∧ acceleratedOrbit 13 2746 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2746 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2746) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2746.1, data_13_2746.2]

/-- Complete interval computation for depth 13, residue 2747. -/
theorem bounds_13_2747 : exactInterval 13 2747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2747 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2747) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2747 : oddCount 2747 13 = 7 ∧ acceleratedOrbit 13 2747 = 734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2747 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2747) = 3 ^ 7 * m + 734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2747.1, data_13_2747.2]

/-- Complete interval computation for depth 13, residue 2748. -/
theorem bounds_13_2748 : exactInterval 13 2748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2748 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2748) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2748 : oddCount 2748 13 = 6 ∧ acceleratedOrbit 13 2748 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2748 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2748) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2748.1, data_13_2748.2]

/-- Complete interval computation for depth 13, residue 2749. -/
theorem bounds_13_2749 : exactInterval 13 2749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2749 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2749) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2749 : oddCount 2749 13 = 6 ∧ acceleratedOrbit 13 2749 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2749 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2749) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2749.1, data_13_2749.2]

/-- Complete interval computation for depth 13, residue 2750. -/
theorem bounds_13_2750 : exactInterval 13 2750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2750 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2750) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2750 : oddCount 2750 13 = 6 ∧ acceleratedOrbit 13 2750 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2750 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2750) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2750.1, data_13_2750.2]

/-- Complete interval computation for depth 13, residue 2751. -/
theorem bounds_13_2751 : exactInterval 13 2751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2751 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2751) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2751 : oddCount 2751 13 = 10 ∧ acceleratedOrbit 13 2751 = 19838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2751 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2751) = 3 ^ 10 * m + 19838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2751.1, data_13_2751.2]

/-- Complete interval computation for depth 13, residue 2752. -/
theorem bounds_13_2752 : exactInterval 13 2752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2752 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2752) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2752 : oddCount 2752 13 = 4 ∧ acceleratedOrbit 13 2752 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2752 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2752) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2752.1, data_13_2752.2]

/-- Complete interval computation for depth 13, residue 2753. -/
theorem bounds_13_2753 : exactInterval 13 2753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2753 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2753) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2753 : oddCount 2753 13 = 5 ∧ acceleratedOrbit 13 2753 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2753 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2753) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2753.1, data_13_2753.2]

end Collatz.Research.StoppingAtlas.Batch0646
