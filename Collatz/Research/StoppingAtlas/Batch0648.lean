import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0648

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2769. -/
theorem bounds_13_2769 : exactInterval 13 2769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2769 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2769) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2769 : oddCount 2769 13 = 6 ∧ acceleratedOrbit 13 2769 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2769 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2769) = 3 ^ 6 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2769.1, data_13_2769.2]

/-- Complete interval computation for depth 13, residue 2770. -/
theorem bounds_13_2770 : exactInterval 13 2770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2770 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2770) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2770 : oddCount 2770 13 = 6 ∧ acceleratedOrbit 13 2770 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2770 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2770) = 3 ^ 6 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2770.1, data_13_2770.2]

/-- Complete interval computation for depth 13, residue 2771. -/
theorem bounds_13_2771 : exactInterval 13 2771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2771 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2771) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2771 : oddCount 2771 13 = 6 ∧ acceleratedOrbit 13 2771 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2771 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2771) = 3 ^ 6 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2771.1, data_13_2771.2]

/-- Complete interval computation for depth 13, residue 2772. -/
theorem bounds_13_2772 : exactInterval 13 2772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2772 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2772) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2772 : oddCount 2772 13 = 4 ∧ acceleratedOrbit 13 2772 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2772 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2772) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2772.1, data_13_2772.2]

/-- Complete interval computation for depth 13, residue 2773. -/
theorem bounds_13_2773 : exactInterval 13 2773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2773 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2773) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2773 : oddCount 2773 13 = 4 ∧ acceleratedOrbit 13 2773 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2773 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2773) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2773.1, data_13_2773.2]

/-- Complete interval computation for depth 13, residue 2774. -/
theorem bounds_13_2774 : exactInterval 13 2774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2774 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2774) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2774 : oddCount 2774 13 = 7 ∧ acceleratedOrbit 13 2774 = 742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2774 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2774) = 3 ^ 7 * m + 742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2774.1, data_13_2774.2]

/-- Complete interval computation for depth 13, residue 2775. -/
theorem bounds_13_2775 : exactInterval 13 2775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2775 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2775) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2775 : oddCount 2775 13 = 7 ∧ acceleratedOrbit 13 2775 = 742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2775 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2775) = 3 ^ 7 * m + 742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2775.1, data_13_2775.2]

/-- Complete interval computation for depth 13, residue 2776. -/
theorem bounds_13_2776 : exactInterval 13 2776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2776 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2776) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2776 : oddCount 2776 13 = 6 ∧ acceleratedOrbit 13 2776 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2776 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2776) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2776.1, data_13_2776.2]

/-- Complete interval computation for depth 13, residue 2777. -/
theorem bounds_13_2777 : exactInterval 13 2777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2777 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2777) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2777 : oddCount 2777 13 = 5 ∧ acceleratedOrbit 13 2777 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2777 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2777) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2777.1, data_13_2777.2]

/-- Complete interval computation for depth 13, residue 2778. -/
theorem bounds_13_2778 : exactInterval 13 2778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2778 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2778) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2778 : oddCount 2778 13 = 6 ∧ acceleratedOrbit 13 2778 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2778 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2778) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2778.1, data_13_2778.2]

/-- Complete interval computation for depth 13, residue 2779. -/
theorem bounds_13_2779 : exactInterval 13 2779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2779 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2779) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2779 : oddCount 2779 13 = 9 ∧ acceleratedOrbit 13 2779 = 6682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2779 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2779) = 3 ^ 9 * m + 6682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2779.1, data_13_2779.2]

/-- Complete interval computation for depth 13, residue 2780. -/
theorem bounds_13_2780 : exactInterval 13 2780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2780 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2780) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2780 : oddCount 2780 13 = 6 ∧ acceleratedOrbit 13 2780 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2780 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2780) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2780.1, data_13_2780.2]

/-- Complete interval computation for depth 13, residue 2781. -/
theorem bounds_13_2781 : exactInterval 13 2781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2781 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2781) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2781 : oddCount 2781 13 = 6 ∧ acceleratedOrbit 13 2781 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2781 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2781) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2781.1, data_13_2781.2]

/-- Complete interval computation for depth 13, residue 2782. -/
theorem bounds_13_2782 : exactInterval 13 2782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2782 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2782) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2782 : oddCount 2782 13 = 8 ∧ acceleratedOrbit 13 2782 = 2231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2782 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2782) = 3 ^ 8 * m + 2231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2782.1, data_13_2782.2]

/-- Complete interval computation for depth 13, residue 2783. -/
theorem bounds_13_2783 : exactInterval 13 2783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2783 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2783) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2783 : oddCount 2783 13 = 8 ∧ acceleratedOrbit 13 2783 = 2231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2783 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2783) = 3 ^ 8 * m + 2231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2783.1, data_13_2783.2]

/-- Complete interval computation for depth 13, residue 2784. -/
theorem bounds_13_2784 : exactInterval 13 2784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2784 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2784) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2784 : oddCount 2784 13 = 4 ∧ acceleratedOrbit 13 2784 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2784 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2784) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2784.1, data_13_2784.2]

end Collatz.Research.StoppingAtlas.Batch0648
