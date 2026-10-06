import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0843

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5765. -/
theorem bounds_13_5765 : exactInterval 13 5765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5765 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5765) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5765 : oddCount 5765 13 = 6 ∧ acceleratedOrbit 13 5765 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5765 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5765) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5765.1, data_13_5765.2]

/-- Complete interval computation for depth 13, residue 5766. -/
theorem bounds_13_5766 : exactInterval 13 5766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5766 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5766) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5766 : oddCount 5766 13 = 6 ∧ acceleratedOrbit 13 5766 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5766 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5766) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5766.1, data_13_5766.2]

/-- Complete interval computation for depth 13, residue 5767. -/
theorem bounds_13_5767 : exactInterval 13 5767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5767 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5767) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5767 : oddCount 5767 13 = 7 ∧ acceleratedOrbit 13 5767 = 1541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5767 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5767) = 3 ^ 7 * m + 1541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5767.1, data_13_5767.2]

/-- Complete interval computation for depth 13, residue 5768. -/
theorem bounds_13_5768 : exactInterval 13 5768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5768 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5768) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5768 : oddCount 5768 13 = 5 ∧ acceleratedOrbit 13 5768 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5768 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5768) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5768.1, data_13_5768.2]

/-- Complete interval computation for depth 13, residue 5769. -/
theorem bounds_13_5769 : exactInterval 13 5769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5769 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5769) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5769 : oddCount 5769 13 = 8 ∧ acceleratedOrbit 13 5769 = 4622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5769 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5769) = 3 ^ 8 * m + 4622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5769.1, data_13_5769.2]

/-- Complete interval computation for depth 13, residue 5770. -/
theorem bounds_13_5770 : exactInterval 13 5770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5770 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5770) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5770 : oddCount 5770 13 = 5 ∧ acceleratedOrbit 13 5770 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5770 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5770) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5770.1, data_13_5770.2]

/-- Complete interval computation for depth 13, residue 5771. -/
theorem bounds_13_5771 : exactInterval 13 5771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5771 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5771) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5771 : oddCount 5771 13 = 6 ∧ acceleratedOrbit 13 5771 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5771 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5771) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5771.1, data_13_5771.2]

/-- Complete interval computation for depth 13, residue 5772. -/
theorem bounds_13_5772 : exactInterval 13 5772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5772 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5772) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5772 : oddCount 5772 13 = 5 ∧ acceleratedOrbit 13 5772 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5772 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5772) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5772.1, data_13_5772.2]

/-- Complete interval computation for depth 13, residue 5773. -/
theorem bounds_13_5773 : exactInterval 13 5773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5773 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5773) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5773 : oddCount 5773 13 = 5 ∧ acceleratedOrbit 13 5773 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5773 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5773) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5773.1, data_13_5773.2]

/-- Complete interval computation for depth 13, residue 5774. -/
theorem bounds_13_5774 : exactInterval 13 5774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5774 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5774) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5774 : oddCount 5774 13 = 8 ∧ acceleratedOrbit 13 5774 = 4627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5774 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5774) = 3 ^ 8 * m + 4627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5774.1, data_13_5774.2]

/-- Complete interval computation for depth 13, residue 5775. -/
theorem bounds_13_5775 : exactInterval 13 5775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5775 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5775) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5775 : oddCount 5775 13 = 8 ∧ acceleratedOrbit 13 5775 = 4627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5775 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5775) = 3 ^ 8 * m + 4627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5775.1, data_13_5775.2]

/-- Complete interval computation for depth 13, residue 5776. -/
theorem bounds_13_5776 : exactInterval 13 5776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5776 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5776) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5776 : oddCount 5776 13 = 5 ∧ acceleratedOrbit 13 5776 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5776 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5776) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5776.1, data_13_5776.2]

/-- Complete interval computation for depth 13, residue 5777. -/
theorem bounds_13_5777 : exactInterval 13 5777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5777 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5777) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5777 : oddCount 5777 13 = 6 ∧ acceleratedOrbit 13 5777 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5777 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5777) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5777.1, data_13_5777.2]

/-- Complete interval computation for depth 13, residue 5778. -/
theorem bounds_13_5778 : exactInterval 13 5778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5778 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5778) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5778 : oddCount 5778 13 = 6 ∧ acceleratedOrbit 13 5778 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5778 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5778) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5778.1, data_13_5778.2]

/-- Complete interval computation for depth 13, residue 5779. -/
theorem bounds_13_5779 : exactInterval 13 5779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5779 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5779) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5779 : oddCount 5779 13 = 6 ∧ acceleratedOrbit 13 5779 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5779 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5779) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5779.1, data_13_5779.2]

end Collatz.Research.StoppingAtlas.Batch0843
