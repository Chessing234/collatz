import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0251

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 768. -/
theorem bounds_12_768 : exactInterval 12 768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_768 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 768) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_768 : oddCount 768 12 = 2 ∧ acceleratedOrbit 12 768 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_768 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 768) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_768.1, data_12_768.2]

/-- Complete interval computation for depth 12, residue 769. -/
theorem bounds_12_769 : exactInterval 12 769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_769 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 769) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_769 : oddCount 769 12 = 5 ∧ acceleratedOrbit 12 769 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_769 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 769) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_769.1, data_12_769.2]

/-- Complete interval computation for depth 12, residue 770. -/
theorem bounds_12_770 : exactInterval 12 770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_770 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 770) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_770 : oddCount 770 12 = 5 ∧ acceleratedOrbit 12 770 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_770 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 770) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_770.1, data_12_770.2]

/-- Complete interval computation for depth 12, residue 771. -/
theorem bounds_12_771 : exactInterval 12 771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_771 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 771) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_771 : oddCount 771 12 = 5 ∧ acceleratedOrbit 12 771 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_771 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 771) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_771.1, data_12_771.2]

/-- Complete interval computation for depth 12, residue 772. -/
theorem bounds_12_772 : exactInterval 12 772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_772 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 772) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_772 : oddCount 772 12 = 5 ∧ acceleratedOrbit 12 772 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_772 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 772) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_772.1, data_12_772.2]

/-- Complete interval computation for depth 12, residue 773. -/
theorem bounds_12_773 : exactInterval 12 773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_773 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 773) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_773 : oddCount 773 12 = 5 ∧ acceleratedOrbit 12 773 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_773 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 773) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_773.1, data_12_773.2]

/-- Complete interval computation for depth 12, residue 774. -/
theorem bounds_12_774 : exactInterval 12 774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_774 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 774) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_774 : oddCount 774 12 = 5 ∧ acceleratedOrbit 12 774 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_774 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 774) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_774.1, data_12_774.2]

/-- Complete interval computation for depth 12, residue 775. -/
theorem bounds_12_775 : exactInterval 12 775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_775 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 775) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_775 : oddCount 775 12 = 7 ∧ acceleratedOrbit 12 775 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_775 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 775) = 3 ^ 7 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_775.1, data_12_775.2]

/-- Complete interval computation for depth 12, residue 776. -/
theorem bounds_12_776 : exactInterval 12 776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_776 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 776) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_776 : oddCount 776 12 = 5 ∧ acceleratedOrbit 12 776 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_776 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 776) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_776.1, data_12_776.2]

/-- Complete interval computation for depth 12, residue 777. -/
theorem bounds_12_777 : exactInterval 12 777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_777 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 777) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_777 : oddCount 777 12 = 7 ∧ acceleratedOrbit 12 777 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_777 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 777) = 3 ^ 7 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_777.1, data_12_777.2]

/-- Complete interval computation for depth 12, residue 778. -/
theorem bounds_12_778 : exactInterval 12 778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_778 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 778) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_778 : oddCount 778 12 = 5 ∧ acceleratedOrbit 12 778 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_778 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 778) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_778.1, data_12_778.2]

/-- Complete interval computation for depth 12, residue 779. -/
theorem bounds_12_779 : exactInterval 12 779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_779 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 779) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_779 : oddCount 779 12 = 7 ∧ acceleratedOrbit 12 779 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_779 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 779) = 3 ^ 7 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_779.1, data_12_779.2]

/-- Complete interval computation for depth 12, residue 780. -/
theorem bounds_12_780 : exactInterval 12 780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_780 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 780) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_780 : oddCount 780 12 = 5 ∧ acceleratedOrbit 12 780 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_780 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 780) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_780.1, data_12_780.2]

/-- Complete interval computation for depth 12, residue 781. -/
theorem bounds_12_781 : exactInterval 12 781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_781 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 781) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_781 : oddCount 781 12 = 5 ∧ acceleratedOrbit 12 781 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_781 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 781) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_781.1, data_12_781.2]

/-- Complete interval computation for depth 12, residue 782. -/
theorem bounds_12_782 : exactInterval 12 782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_782 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 782) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_782 : oddCount 782 12 = 5 ∧ acceleratedOrbit 12 782 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_782 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 782) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_782.1, data_12_782.2]

end Collatz.Research.StoppingAtlas.Batch0251
