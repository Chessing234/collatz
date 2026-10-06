import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0118

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 773. -/
theorem bounds_11_773 : exactInterval 11 773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_773 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 773) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_773 : oddCount 773 11 = 4 ∧ acceleratedOrbit 11 773 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_773 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 773) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_773.1, data_11_773.2]

/-- Complete interval computation for depth 11, residue 774. -/
theorem bounds_11_774 : exactInterval 11 774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_774 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 774) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_774 : oddCount 774 11 = 4 ∧ acceleratedOrbit 11 774 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_774 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 774) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_774.1, data_11_774.2]

/-- Complete interval computation for depth 11, residue 775. -/
theorem bounds_11_775 : exactInterval 11 775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_775 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 775) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_775 : oddCount 775 11 = 7 ∧ acceleratedOrbit 11 775 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_775 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 775) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_775.1, data_11_775.2]

/-- Complete interval computation for depth 11, residue 776. -/
theorem bounds_11_776 : exactInterval 11 776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_776 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 776) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_776 : oddCount 776 11 = 5 ∧ acceleratedOrbit 11 776 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_776 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 776) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_776.1, data_11_776.2]

/-- Complete interval computation for depth 11, residue 777. -/
theorem bounds_11_777 : exactInterval 11 777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_777 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 777) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_777 : oddCount 777 11 = 7 ∧ acceleratedOrbit 11 777 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_777 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 777) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_777.1, data_11_777.2]

/-- Complete interval computation for depth 11, residue 778. -/
theorem bounds_11_778 : exactInterval 11 778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_778 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 778) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_778 : oddCount 778 11 = 5 ∧ acceleratedOrbit 11 778 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_778 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 778) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_778.1, data_11_778.2]

/-- Complete interval computation for depth 11, residue 779. -/
theorem bounds_11_779 : exactInterval 11 779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_779 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 779) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_779 : oddCount 779 11 = 7 ∧ acceleratedOrbit 11 779 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_779 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 779) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_779.1, data_11_779.2]

/-- Complete interval computation for depth 11, residue 780. -/
theorem bounds_11_780 : exactInterval 11 780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_780 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 780) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_780 : oddCount 780 11 = 5 ∧ acceleratedOrbit 11 780 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_780 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 780) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_780.1, data_11_780.2]

/-- Complete interval computation for depth 11, residue 781. -/
theorem bounds_11_781 : exactInterval 11 781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_781 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 781) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_781 : oddCount 781 11 = 5 ∧ acceleratedOrbit 11 781 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_781 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 781) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_781.1, data_11_781.2]

/-- Complete interval computation for depth 11, residue 782. -/
theorem bounds_11_782 : exactInterval 11 782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_782 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 782) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_782 : oddCount 782 11 = 4 ∧ acceleratedOrbit 11 782 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_782 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 782) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_782.1, data_11_782.2]

/-- Complete interval computation for depth 11, residue 783. -/
theorem bounds_11_783 : exactInterval 11 783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_783 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 783) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_783 : oddCount 783 11 = 4 ∧ acceleratedOrbit 11 783 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_783 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 783) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_783.1, data_11_783.2]

/-- Complete interval computation for depth 11, residue 784. -/
theorem bounds_11_784 : exactInterval 11 784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_784 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 784) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_784 : oddCount 784 11 = 3 ∧ acceleratedOrbit 11 784 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_784 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 784) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_784.1, data_11_784.2]

/-- Complete interval computation for depth 11, residue 785. -/
theorem bounds_11_785 : exactInterval 11 785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_785 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 785) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_785 : oddCount 785 11 = 5 ∧ acceleratedOrbit 11 785 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_785 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 785) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_785.1, data_11_785.2]

/-- Complete interval computation for depth 11, residue 786. -/
theorem bounds_11_786 : exactInterval 11 786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_786 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 786) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_786 : oddCount 786 11 = 6 ∧ acceleratedOrbit 11 786 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_786 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 786) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_786.1, data_11_786.2]

/-- Complete interval computation for depth 11, residue 787. -/
theorem bounds_11_787 : exactInterval 11 787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_787 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 787) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_787 : oddCount 787 11 = 6 ∧ acceleratedOrbit 11 787 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_787 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 787) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_787.1, data_11_787.2]

end Collatz.Research.StoppingAtlas.Batch0118
