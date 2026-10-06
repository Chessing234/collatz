import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0849

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5857. -/
theorem bounds_13_5857 : exactInterval 13 5857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5857 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5857) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5857 : oddCount 5857 13 = 8 ∧ acceleratedOrbit 13 5857 = 4693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5857 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5857) = 3 ^ 8 * m + 4693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5857.1, data_13_5857.2]

/-- Complete interval computation for depth 13, residue 5858. -/
theorem bounds_13_5858 : exactInterval 13 5858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5858 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5858) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5858 : oddCount 5858 13 = 5 ∧ acceleratedOrbit 13 5858 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5858 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5858) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5858.1, data_13_5858.2]

/-- Complete interval computation for depth 13, residue 5859. -/
theorem bounds_13_5859 : exactInterval 13 5859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5859 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5859) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5859 : oddCount 5859 13 = 5 ∧ acceleratedOrbit 13 5859 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5859 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5859) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5859.1, data_13_5859.2]

/-- Complete interval computation for depth 13, residue 5860. -/
theorem bounds_13_5860 : exactInterval 13 5860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5860 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5860) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5860 : oddCount 5860 13 = 4 ∧ acceleratedOrbit 13 5860 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5860 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5860) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5860.1, data_13_5860.2]

/-- Complete interval computation for depth 13, residue 5861. -/
theorem bounds_13_5861 : exactInterval 13 5861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5861 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5861) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5861 : oddCount 5861 13 = 4 ∧ acceleratedOrbit 13 5861 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5861 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5861) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5861.1, data_13_5861.2]

/-- Complete interval computation for depth 13, residue 5862. -/
theorem bounds_13_5862 : exactInterval 13 5862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5862 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5862) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5862 : oddCount 5862 13 = 4 ∧ acceleratedOrbit 13 5862 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5862 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5862) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5862.1, data_13_5862.2]

/-- Complete interval computation for depth 13, residue 5863. -/
theorem bounds_13_5863 : exactInterval 13 5863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5863 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5863) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5863 : oddCount 5863 13 = 10 ∧ acceleratedOrbit 13 5863 = 42272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5863 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5863) = 3 ^ 10 * m + 42272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5863.1, data_13_5863.2]

/-- Complete interval computation for depth 13, residue 5864. -/
theorem bounds_13_5864 : exactInterval 13 5864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5864 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5864) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5864 : oddCount 5864 13 = 5 ∧ acceleratedOrbit 13 5864 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5864 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5864) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5864.1, data_13_5864.2]

/-- Complete interval computation for depth 13, residue 5865. -/
theorem bounds_13_5865 : exactInterval 13 5865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5865 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5865) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5865 : oddCount 5865 13 = 8 ∧ acceleratedOrbit 13 5865 = 4699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5865 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5865) = 3 ^ 8 * m + 4699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5865.1, data_13_5865.2]

/-- Complete interval computation for depth 13, residue 5866. -/
theorem bounds_13_5866 : exactInterval 13 5866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5866 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5866) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5866 : oddCount 5866 13 = 5 ∧ acceleratedOrbit 13 5866 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5866 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5866) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5866.1, data_13_5866.2]

/-- Complete interval computation for depth 13, residue 5867. -/
theorem bounds_13_5867 : exactInterval 13 5867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5867 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5867) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5867 : oddCount 5867 13 = 7 ∧ acceleratedOrbit 13 5867 = 1567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5867 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5867) = 3 ^ 7 * m + 1567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5867.1, data_13_5867.2]

/-- Complete interval computation for depth 13, residue 5868. -/
theorem bounds_13_5868 : exactInterval 13 5868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5868 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5868) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5868 : oddCount 5868 13 = 6 ∧ acceleratedOrbit 13 5868 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5868 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5868) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5868.1, data_13_5868.2]

/-- Complete interval computation for depth 13, residue 5869. -/
theorem bounds_13_5869 : exactInterval 13 5869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5869 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5869) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5869 : oddCount 5869 13 = 6 ∧ acceleratedOrbit 13 5869 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5869 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5869) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5869.1, data_13_5869.2]

/-- Complete interval computation for depth 13, residue 5870. -/
theorem bounds_13_5870 : exactInterval 13 5870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5870 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5870) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5870 : oddCount 5870 13 = 6 ∧ acceleratedOrbit 13 5870 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5870 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5870) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5870.1, data_13_5870.2]

/-- Complete interval computation for depth 13, residue 5871. -/
theorem bounds_13_5871 : exactInterval 13 5871 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5871 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5871) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5871 : oddCount 5871 13 = 8 ∧ acceleratedOrbit 13 5871 = 4703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5871 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5871) = 3 ^ 8 * m + 4703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5871.1, data_13_5871.2]

end Collatz.Research.StoppingAtlas.Batch0849
