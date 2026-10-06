import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0713

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3768. -/
theorem bounds_13_3768 : exactInterval 13 3768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3768 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3768) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3768 : oddCount 3768 13 = 6 ∧ acceleratedOrbit 13 3768 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3768 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3768) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3768.1, data_13_3768.2]

/-- Complete interval computation for depth 13, residue 3769. -/
theorem bounds_13_3769 : exactInterval 13 3769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3769 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3769) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3769 : oddCount 3769 13 = 8 ∧ acceleratedOrbit 13 3769 = 3023 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3769 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3769) = 3 ^ 8 * m + 3023 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3769.1, data_13_3769.2]

/-- Complete interval computation for depth 13, residue 3770. -/
theorem bounds_13_3770 : exactInterval 13 3770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3770 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3770) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3770 : oddCount 3770 13 = 6 ∧ acceleratedOrbit 13 3770 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3770 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3770) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3770.1, data_13_3770.2]

/-- Complete interval computation for depth 13, residue 3771. -/
theorem bounds_13_3771 : exactInterval 13 3771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3771 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3771) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3771 : oddCount 3771 13 = 8 ∧ acceleratedOrbit 13 3771 = 3023 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3771 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3771) = 3 ^ 8 * m + 3023 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3771.1, data_13_3771.2]

/-- Complete interval computation for depth 13, residue 3772. -/
theorem bounds_13_3772 : exactInterval 13 3772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3772 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3772) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3772 : oddCount 3772 13 = 5 ∧ acceleratedOrbit 13 3772 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3772 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3772) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3772.1, data_13_3772.2]

/-- Complete interval computation for depth 13, residue 3773. -/
theorem bounds_13_3773 : exactInterval 13 3773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3773 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3773) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3773 : oddCount 3773 13 = 5 ∧ acceleratedOrbit 13 3773 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3773 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3773) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3773.1, data_13_3773.2]

/-- Complete interval computation for depth 13, residue 3774. -/
theorem bounds_13_3774 : exactInterval 13 3774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3774 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3774) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3774 : oddCount 3774 13 = 5 ∧ acceleratedOrbit 13 3774 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3774 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3774) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3774.1, data_13_3774.2]

/-- Complete interval computation for depth 13, residue 3775. -/
theorem bounds_13_3775 : exactInterval 13 3775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3775 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3775) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3775 : oddCount 3775 13 = 9 ∧ acceleratedOrbit 13 3775 = 9073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3775 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3775) = 3 ^ 9 * m + 9073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3775.1, data_13_3775.2]

/-- Complete interval computation for depth 13, residue 3776. -/
theorem bounds_13_3776 : exactInterval 13 3776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3776 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3776) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3776 : oddCount 3776 13 = 4 ∧ acceleratedOrbit 13 3776 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3776 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3776) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3776.1, data_13_3776.2]

/-- Complete interval computation for depth 13, residue 3777. -/
theorem bounds_13_3777 : exactInterval 13 3777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3777 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3777) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3777 : oddCount 3777 13 = 6 ∧ acceleratedOrbit 13 3777 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3777 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3777) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3777.1, data_13_3777.2]

/-- Complete interval computation for depth 13, residue 3778. -/
theorem bounds_13_3778 : exactInterval 13 3778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3778 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3778) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3778 : oddCount 3778 13 = 7 ∧ acceleratedOrbit 13 3778 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3778 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3778) = 3 ^ 7 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3778.1, data_13_3778.2]

/-- Complete interval computation for depth 13, residue 3779. -/
theorem bounds_13_3779 : exactInterval 13 3779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3779 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3779) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3779 : oddCount 3779 13 = 7 ∧ acceleratedOrbit 13 3779 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3779 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3779) = 3 ^ 7 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3779.1, data_13_3779.2]

/-- Complete interval computation for depth 13, residue 3780. -/
theorem bounds_13_3780 : exactInterval 13 3780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3780 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3780) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3780 : oddCount 3780 13 = 4 ∧ acceleratedOrbit 13 3780 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3780 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3780) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3780.1, data_13_3780.2]

/-- Complete interval computation for depth 13, residue 3781. -/
theorem bounds_13_3781 : exactInterval 13 3781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3781 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3781) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3781 : oddCount 3781 13 = 4 ∧ acceleratedOrbit 13 3781 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3781 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3781) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3781.1, data_13_3781.2]

/-- Complete interval computation for depth 13, residue 3782. -/
theorem bounds_13_3782 : exactInterval 13 3782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3782 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3782) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3782 : oddCount 3782 13 = 4 ∧ acceleratedOrbit 13 3782 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3782 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3782) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3782.1, data_13_3782.2]

end Collatz.Research.StoppingAtlas.Batch0713
