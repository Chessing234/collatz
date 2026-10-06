import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0914

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6855. -/
theorem bounds_13_6855 : exactInterval 13 6855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6855 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6855) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6855 : oddCount 6855 13 = 7 ∧ acceleratedOrbit 13 6855 = 1831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6855 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6855) = 3 ^ 7 * m + 1831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6855.1, data_13_6855.2]

/-- Complete interval computation for depth 13, residue 6856. -/
theorem bounds_13_6856 : exactInterval 13 6856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6856 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6856) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6856 : oddCount 6856 13 = 4 ∧ acceleratedOrbit 13 6856 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6856 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6856) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6856.1, data_13_6856.2]

/-- Complete interval computation for depth 13, residue 6857. -/
theorem bounds_13_6857 : exactInterval 13 6857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6857 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6857) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6857 : oddCount 6857 13 = 6 ∧ acceleratedOrbit 13 6857 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6857 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6857) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6857.1, data_13_6857.2]

/-- Complete interval computation for depth 13, residue 6858. -/
theorem bounds_13_6858 : exactInterval 13 6858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6858 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6858) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6858 : oddCount 6858 13 = 4 ∧ acceleratedOrbit 13 6858 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6858 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6858) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6858.1, data_13_6858.2]

/-- Complete interval computation for depth 13, residue 6859. -/
theorem bounds_13_6859 : exactInterval 13 6859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6859 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6859) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6859 : oddCount 6859 13 = 8 ∧ acceleratedOrbit 13 6859 = 5498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6859 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6859) = 3 ^ 8 * m + 5498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6859.1, data_13_6859.2]

/-- Complete interval computation for depth 13, residue 6860. -/
theorem bounds_13_6860 : exactInterval 13 6860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6860 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6860) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6860 : oddCount 6860 13 = 4 ∧ acceleratedOrbit 13 6860 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6860 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6860) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6860.1, data_13_6860.2]

/-- Complete interval computation for depth 13, residue 6861. -/
theorem bounds_13_6861 : exactInterval 13 6861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6861 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6861) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6861 : oddCount 6861 13 = 4 ∧ acceleratedOrbit 13 6861 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6861 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6861) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6861.1, data_13_6861.2]

/-- Complete interval computation for depth 13, residue 6862. -/
theorem bounds_13_6862 : exactInterval 13 6862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6862 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6862) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6862 : oddCount 6862 13 = 10 ∧ acceleratedOrbit 13 6862 = 49481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6862 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6862) = 3 ^ 10 * m + 49481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6862.1, data_13_6862.2]

/-- Complete interval computation for depth 13, residue 6863. -/
theorem bounds_13_6863 : exactInterval 13 6863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6863 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6863) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6863 : oddCount 6863 13 = 10 ∧ acceleratedOrbit 13 6863 = 49481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6863 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6863) = 3 ^ 10 * m + 49481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6863.1, data_13_6863.2]

/-- Complete interval computation for depth 13, residue 6864. -/
theorem bounds_13_6864 : exactInterval 13 6864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6864 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6864) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6864 : oddCount 6864 13 = 5 ∧ acceleratedOrbit 13 6864 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6864 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6864) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6864.1, data_13_6864.2]

/-- Complete interval computation for depth 13, residue 6865. -/
theorem bounds_13_6865 : exactInterval 13 6865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6865 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6865) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6865 : oddCount 6865 13 = 7 ∧ acceleratedOrbit 13 6865 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6865 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6865) = 3 ^ 7 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6865.1, data_13_6865.2]

/-- Complete interval computation for depth 13, residue 6866. -/
theorem bounds_13_6866 : exactInterval 13 6866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6866 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6866) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6866 : oddCount 6866 13 = 7 ∧ acceleratedOrbit 13 6866 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6866 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6866) = 3 ^ 7 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6866.1, data_13_6866.2]

/-- Complete interval computation for depth 13, residue 6867. -/
theorem bounds_13_6867 : exactInterval 13 6867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6867 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6867) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6867 : oddCount 6867 13 = 7 ∧ acceleratedOrbit 13 6867 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6867 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6867) = 3 ^ 7 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6867.1, data_13_6867.2]

/-- Complete interval computation for depth 13, residue 6868. -/
theorem bounds_13_6868 : exactInterval 13 6868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6868 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6868) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6868 : oddCount 6868 13 = 5 ∧ acceleratedOrbit 13 6868 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6868 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6868) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6868.1, data_13_6868.2]

/-- Complete interval computation for depth 13, residue 6869. -/
theorem bounds_13_6869 : exactInterval 13 6869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6869 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6869) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6869 : oddCount 6869 13 = 5 ∧ acceleratedOrbit 13 6869 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6869 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6869) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6869.1, data_13_6869.2]

/-- Complete interval computation for depth 13, residue 6870. -/
theorem bounds_13_6870 : exactInterval 13 6870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6870 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6870) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6870 : oddCount 6870 13 = 8 ∧ acceleratedOrbit 13 6870 = 5507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6870 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6870) = 3 ^ 8 * m + 5507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6870.1, data_13_6870.2]

end Collatz.Research.StoppingAtlas.Batch0914
