import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0381

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2764. -/
theorem bounds_12_2764 : exactInterval 12 2764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2764 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2764) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2764 : oddCount 2764 12 = 4 ∧ acceleratedOrbit 12 2764 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2764 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2764) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2764.1, data_12_2764.2]

/-- Complete interval computation for depth 12, residue 2765. -/
theorem bounds_12_2765 : exactInterval 12 2765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2765 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2765) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2765 : oddCount 2765 12 = 4 ∧ acceleratedOrbit 12 2765 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2765 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2765) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2765.1, data_12_2765.2]

/-- Complete interval computation for depth 12, residue 2766. -/
theorem bounds_12_2766 : exactInterval 12 2766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2766 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2766) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2766 : oddCount 2766 12 = 9 ∧ acceleratedOrbit 12 2766 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2766 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2766) = 3 ^ 9 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2766.1, data_12_2766.2]

/-- Complete interval computation for depth 12, residue 2767. -/
theorem bounds_12_2767 : exactInterval 12 2767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2767 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2767) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2767 : oddCount 2767 12 = 9 ∧ acceleratedOrbit 12 2767 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2767 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2767) = 3 ^ 9 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2767.1, data_12_2767.2]

/-- Complete interval computation for depth 12, residue 2768. -/
theorem bounds_12_2768 : exactInterval 12 2768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2768 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2768) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2768 : oddCount 2768 12 = 4 ∧ acceleratedOrbit 12 2768 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2768 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2768) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2768.1, data_12_2768.2]

/-- Complete interval computation for depth 12, residue 2769. -/
theorem bounds_12_2769 : exactInterval 12 2769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2769 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2769) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2769 : oddCount 2769 12 = 6 ∧ acceleratedOrbit 12 2769 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2769 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2769) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2769.1, data_12_2769.2]

/-- Complete interval computation for depth 12, residue 2770. -/
theorem bounds_12_2770 : exactInterval 12 2770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2770 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2770) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2770 : oddCount 2770 12 = 6 ∧ acceleratedOrbit 12 2770 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2770 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2770) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2770.1, data_12_2770.2]

/-- Complete interval computation for depth 12, residue 2771. -/
theorem bounds_12_2771 : exactInterval 12 2771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2771 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2771) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2771 : oddCount 2771 12 = 6 ∧ acceleratedOrbit 12 2771 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2771 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2771) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2771.1, data_12_2771.2]

/-- Complete interval computation for depth 12, residue 2772. -/
theorem bounds_12_2772 : exactInterval 12 2772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2772 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2772) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2772 : oddCount 2772 12 = 4 ∧ acceleratedOrbit 12 2772 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2772 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2772) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2772.1, data_12_2772.2]

/-- Complete interval computation for depth 12, residue 2773. -/
theorem bounds_12_2773 : exactInterval 12 2773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2773 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2773) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2773 : oddCount 2773 12 = 4 ∧ acceleratedOrbit 12 2773 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2773 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2773) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2773.1, data_12_2773.2]

/-- Complete interval computation for depth 12, residue 2774. -/
theorem bounds_12_2774 : exactInterval 12 2774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2774 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2774) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2774 : oddCount 2774 12 = 7 ∧ acceleratedOrbit 12 2774 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2774 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2774) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2774.1, data_12_2774.2]

/-- Complete interval computation for depth 12, residue 2775. -/
theorem bounds_12_2775 : exactInterval 12 2775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2775 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2775) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2775 : oddCount 2775 12 = 7 ∧ acceleratedOrbit 12 2775 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2775 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2775) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2775.1, data_12_2775.2]

/-- Complete interval computation for depth 12, residue 2776. -/
theorem bounds_12_2776 : exactInterval 12 2776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2776 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2776) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2776 : oddCount 2776 12 = 6 ∧ acceleratedOrbit 12 2776 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2776 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2776) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2776.1, data_12_2776.2]

/-- Complete interval computation for depth 12, residue 2777. -/
theorem bounds_12_2777 : exactInterval 12 2777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2777 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2777) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2777 : oddCount 2777 12 = 4 ∧ acceleratedOrbit 12 2777 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2777 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2777) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2777.1, data_12_2777.2]

/-- Complete interval computation for depth 12, residue 2778. -/
theorem bounds_12_2778 : exactInterval 12 2778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2778 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2778) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2778 : oddCount 2778 12 = 6 ∧ acceleratedOrbit 12 2778 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2778 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2778) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2778.1, data_12_2778.2]

/-- Complete interval computation for depth 12, residue 2779. -/
theorem bounds_12_2779 : exactInterval 12 2779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2779 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2779) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2779 : oddCount 2779 12 = 9 ∧ acceleratedOrbit 12 2779 = 13364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2779 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2779) = 3 ^ 9 * m + 13364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2779.1, data_12_2779.2]

end Collatz.Research.StoppingAtlas.Batch0381
