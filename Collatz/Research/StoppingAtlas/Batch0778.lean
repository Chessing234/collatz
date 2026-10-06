import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0778

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4766. -/
theorem bounds_13_4766 : exactInterval 13 4766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4766 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4766) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4766 : oddCount 4766 13 = 8 ∧ acceleratedOrbit 13 4766 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4766 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4766) = 3 ^ 8 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4766.1, data_13_4766.2]

/-- Complete interval computation for depth 13, residue 4767. -/
theorem bounds_13_4767 : exactInterval 13 4767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4767 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4767) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4767 : oddCount 4767 13 = 10 ∧ acceleratedOrbit 13 4767 = 34370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4767 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4767) = 3 ^ 10 * m + 34370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4767.1, data_13_4767.2]

/-- Complete interval computation for depth 13, residue 4768. -/
theorem bounds_13_4768 : exactInterval 13 4768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4768 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4768) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4768 : oddCount 4768 13 = 3 ∧ acceleratedOrbit 13 4768 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4768 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4768) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4768.1, data_13_4768.2]

/-- Complete interval computation for depth 13, residue 4769. -/
theorem bounds_13_4769 : exactInterval 13 4769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4769 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4769) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4769 : oddCount 4769 13 = 7 ∧ acceleratedOrbit 13 4769 = 1274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4769 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4769) = 3 ^ 7 * m + 1274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4769.1, data_13_4769.2]

/-- Complete interval computation for depth 13, residue 4770. -/
theorem bounds_13_4770 : exactInterval 13 4770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4770 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4770) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4770 : oddCount 4770 13 = 8 ∧ acceleratedOrbit 13 4770 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4770 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4770) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4770.1, data_13_4770.2]

/-- Complete interval computation for depth 13, residue 4771. -/
theorem bounds_13_4771 : exactInterval 13 4771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4771 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4771) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4771 : oddCount 4771 13 = 8 ∧ acceleratedOrbit 13 4771 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4771 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4771) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4771.1, data_13_4771.2]

/-- Complete interval computation for depth 13, residue 4772. -/
theorem bounds_13_4772 : exactInterval 13 4772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4772 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4772) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4772 : oddCount 4772 13 = 8 ∧ acceleratedOrbit 13 4772 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4772 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4772) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4772.1, data_13_4772.2]

/-- Complete interval computation for depth 13, residue 4773. -/
theorem bounds_13_4773 : exactInterval 13 4773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4773 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4773) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4773 : oddCount 4773 13 = 8 ∧ acceleratedOrbit 13 4773 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4773 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4773) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4773.1, data_13_4773.2]

/-- Complete interval computation for depth 13, residue 4774. -/
theorem bounds_13_4774 : exactInterval 13 4774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4774 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4774) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4774 : oddCount 4774 13 = 8 ∧ acceleratedOrbit 13 4774 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4774 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4774) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4774.1, data_13_4774.2]

/-- Complete interval computation for depth 13, residue 4775. -/
theorem bounds_13_4775 : exactInterval 13 4775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4775 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4775) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4775 : oddCount 4775 13 = 9 ∧ acceleratedOrbit 13 4775 = 11477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4775 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4775) = 3 ^ 9 * m + 11477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4775.1, data_13_4775.2]

/-- Complete interval computation for depth 13, residue 4776. -/
theorem bounds_13_4776 : exactInterval 13 4776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4776 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4776) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4776 : oddCount 4776 13 = 3 ∧ acceleratedOrbit 13 4776 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4776 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4776) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4776.1, data_13_4776.2]

/-- Complete interval computation for depth 13, residue 4777. -/
theorem bounds_13_4777 : exactInterval 13 4777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4777 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4777) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4777 : oddCount 4777 13 = 10 ∧ acceleratedOrbit 13 4777 = 34445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4777 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4777) = 3 ^ 10 * m + 34445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4777.1, data_13_4777.2]

/-- Complete interval computation for depth 13, residue 4778. -/
theorem bounds_13_4778 : exactInterval 13 4778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4778 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4778) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4778 : oddCount 4778 13 = 3 ∧ acceleratedOrbit 13 4778 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4778 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4778) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4778.1, data_13_4778.2]

/-- Complete interval computation for depth 13, residue 4779. -/
theorem bounds_13_4779 : exactInterval 13 4779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4779 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4779) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4779 : oddCount 4779 13 = 7 ∧ acceleratedOrbit 13 4779 = 1277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4779 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4779) = 3 ^ 7 * m + 1277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4779.1, data_13_4779.2]

/-- Complete interval computation for depth 13, residue 4780. -/
theorem bounds_13_4780 : exactInterval 13 4780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4780 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4780) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4780 : oddCount 4780 13 = 5 ∧ acceleratedOrbit 13 4780 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4780 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4780) = 3 ^ 5 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4780.1, data_13_4780.2]

/-- Complete interval computation for depth 13, residue 4781. -/
theorem bounds_13_4781 : exactInterval 13 4781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4781 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4781) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4781 : oddCount 4781 13 = 5 ∧ acceleratedOrbit 13 4781 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4781 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4781) = 3 ^ 5 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4781.1, data_13_4781.2]

end Collatz.Research.StoppingAtlas.Batch0778
