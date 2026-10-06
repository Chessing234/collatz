import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0518

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 773. -/
theorem bounds_13_773 : exactInterval 13 773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_773 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 773) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_773 : oddCount 773 13 = 6 ∧ acceleratedOrbit 13 773 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_773 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 773) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_773.1, data_13_773.2]

/-- Complete interval computation for depth 13, residue 774. -/
theorem bounds_13_774 : exactInterval 13 774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_774 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 774) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_774 : oddCount 774 13 = 6 ∧ acceleratedOrbit 13 774 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_774 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 774) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_774.1, data_13_774.2]

/-- Complete interval computation for depth 13, residue 775. -/
theorem bounds_13_775 : exactInterval 13 775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_775 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 775) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_775 : oddCount 775 13 = 8 ∧ acceleratedOrbit 13 775 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_775 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 775) = 3 ^ 8 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_775.1, data_13_775.2]

/-- Complete interval computation for depth 13, residue 776. -/
theorem bounds_13_776 : exactInterval 13 776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_776 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 776) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_776 : oddCount 776 13 = 6 ∧ acceleratedOrbit 13 776 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_776 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 776) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_776.1, data_13_776.2]

/-- Complete interval computation for depth 13, residue 777. -/
theorem bounds_13_777 : exactInterval 13 777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_777 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 777) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_777 : oddCount 777 13 = 7 ∧ acceleratedOrbit 13 777 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_777 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 777) = 3 ^ 7 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_777.1, data_13_777.2]

/-- Complete interval computation for depth 13, residue 778. -/
theorem bounds_13_778 : exactInterval 13 778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_778 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 778) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_778 : oddCount 778 13 = 6 ∧ acceleratedOrbit 13 778 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_778 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 778) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_778.1, data_13_778.2]

/-- Complete interval computation for depth 13, residue 779. -/
theorem bounds_13_779 : exactInterval 13 779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_779 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 779) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_779 : oddCount 779 13 = 7 ∧ acceleratedOrbit 13 779 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_779 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 779) = 3 ^ 7 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_779.1, data_13_779.2]

/-- Complete interval computation for depth 13, residue 780. -/
theorem bounds_13_780 : exactInterval 13 780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_780 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 780) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_780 : oddCount 780 13 = 6 ∧ acceleratedOrbit 13 780 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_780 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 780) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_780.1, data_13_780.2]

/-- Complete interval computation for depth 13, residue 781. -/
theorem bounds_13_781 : exactInterval 13 781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_781 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 781) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_781 : oddCount 781 13 = 6 ∧ acceleratedOrbit 13 781 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_781 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 781) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_781.1, data_13_781.2]

/-- Complete interval computation for depth 13, residue 782. -/
theorem bounds_13_782 : exactInterval 13 782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_782 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 782) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_782 : oddCount 782 13 = 6 ∧ acceleratedOrbit 13 782 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_782 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 782) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_782.1, data_13_782.2]

/-- Complete interval computation for depth 13, residue 783. -/
theorem bounds_13_783 : exactInterval 13 783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_783 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 783) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_783 : oddCount 783 13 = 6 ∧ acceleratedOrbit 13 783 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_783 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 783) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_783.1, data_13_783.2]

/-- Complete interval computation for depth 13, residue 784. -/
theorem bounds_13_784 : exactInterval 13 784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_784 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 784) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_784 : oddCount 784 13 = 5 ∧ acceleratedOrbit 13 784 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_784 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 784) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_784.1, data_13_784.2]

/-- Complete interval computation for depth 13, residue 785. -/
theorem bounds_13_785 : exactInterval 13 785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_785 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 785) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_785 : oddCount 785 13 = 6 ∧ acceleratedOrbit 13 785 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_785 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 785) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_785.1, data_13_785.2]

/-- Complete interval computation for depth 13, residue 786. -/
theorem bounds_13_786 : exactInterval 13 786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_786 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 786) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_786 : oddCount 786 13 = 7 ∧ acceleratedOrbit 13 786 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_786 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 786) = 3 ^ 7 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_786.1, data_13_786.2]

/-- Complete interval computation for depth 13, residue 787. -/
theorem bounds_13_787 : exactInterval 13 787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_787 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 787) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_787 : oddCount 787 13 = 7 ∧ acceleratedOrbit 13 787 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_787 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 787) = 3 ^ 7 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_787.1, data_13_787.2]

end Collatz.Research.StoppingAtlas.Batch0518
