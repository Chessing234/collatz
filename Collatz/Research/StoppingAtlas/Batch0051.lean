import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0051

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 768. -/
theorem bounds_10_768 : exactInterval 10 768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_768 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 768) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_768 : oddCount 768 10 = 2 ∧ acceleratedOrbit 10 768 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_768 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 768) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_768.1, data_10_768.2]

/-- Complete interval computation for depth 10, residue 769. -/
theorem bounds_10_769 : exactInterval 10 769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_769 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 769) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_769 : oddCount 769 10 = 4 ∧ acceleratedOrbit 10 769 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_769 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 769) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_769.1, data_10_769.2]

/-- Complete interval computation for depth 10, residue 770. -/
theorem bounds_10_770 : exactInterval 10 770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_770 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 770) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_770 : oddCount 770 10 = 5 ∧ acceleratedOrbit 10 770 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_770 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 770) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_770.1, data_10_770.2]

/-- Complete interval computation for depth 10, residue 771. -/
theorem bounds_10_771 : exactInterval 10 771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_771 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 771) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_771 : oddCount 771 10 = 5 ∧ acceleratedOrbit 10 771 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_771 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 771) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_771.1, data_10_771.2]

/-- Complete interval computation for depth 10, residue 772. -/
theorem bounds_10_772 : exactInterval 10 772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_772 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 772) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_772 : oddCount 772 10 = 4 ∧ acceleratedOrbit 10 772 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_772 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 772) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_772.1, data_10_772.2]

/-- Complete interval computation for depth 10, residue 773. -/
theorem bounds_10_773 : exactInterval 10 773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_773 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 773) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_773 : oddCount 773 10 = 4 ∧ acceleratedOrbit 10 773 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_773 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 773) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_773.1, data_10_773.2]

/-- Complete interval computation for depth 10, residue 774. -/
theorem bounds_10_774 : exactInterval 10 774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_774 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 774) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_774 : oddCount 774 10 = 4 ∧ acceleratedOrbit 10 774 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_774 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 774) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_774.1, data_10_774.2]

/-- Complete interval computation for depth 10, residue 775. -/
theorem bounds_10_775 : exactInterval 10 775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_775 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 775) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_775 : oddCount 775 10 = 6 ∧ acceleratedOrbit 10 775 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_775 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 775) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_775.1, data_10_775.2]

/-- Complete interval computation for depth 10, residue 776. -/
theorem bounds_10_776 : exactInterval 10 776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_776 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 776) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_776 : oddCount 776 10 = 5 ∧ acceleratedOrbit 10 776 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_776 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 776) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_776.1, data_10_776.2]

/-- Complete interval computation for depth 10, residue 777. -/
theorem bounds_10_777 : exactInterval 10 777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_777 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 777) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_777 : oddCount 777 10 = 7 ∧ acceleratedOrbit 10 777 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_777 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 777) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_777.1, data_10_777.2]

/-- Complete interval computation for depth 10, residue 778. -/
theorem bounds_10_778 : exactInterval 10 778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_778 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 778) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_778 : oddCount 778 10 = 5 ∧ acceleratedOrbit 10 778 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_778 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 778) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_778.1, data_10_778.2]

/-- Complete interval computation for depth 10, residue 779. -/
theorem bounds_10_779 : exactInterval 10 779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_779 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 779) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_779 : oddCount 779 10 = 6 ∧ acceleratedOrbit 10 779 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_779 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 779) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_779.1, data_10_779.2]

/-- Complete interval computation for depth 10, residue 780. -/
theorem bounds_10_780 : exactInterval 10 780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_780 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 780) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_780 : oddCount 780 10 = 5 ∧ acceleratedOrbit 10 780 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_780 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 780) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_780.1, data_10_780.2]

/-- Complete interval computation for depth 10, residue 781. -/
theorem bounds_10_781 : exactInterval 10 781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_781 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 781) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_781 : oddCount 781 10 = 5 ∧ acceleratedOrbit 10 781 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_781 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 781) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_781.1, data_10_781.2]

/-- Complete interval computation for depth 10, residue 782. -/
theorem bounds_10_782 : exactInterval 10 782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_782 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 782) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_782 : oddCount 782 10 = 4 ∧ acceleratedOrbit 10 782 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_782 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 782) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_782.1, data_10_782.2]

end Collatz.Research.StoppingAtlas.Batch0051
