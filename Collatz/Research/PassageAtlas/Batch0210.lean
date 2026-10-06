import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0210

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6848. -/
theorem bounds_15_6848 : exactInterval 15 6848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6848 : oddCount 6848 15 = 6 ∧ acceleratedOrbit 15 6848 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6848) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6848.1, data_15_6848.2]

/-- Complete interval computation for depth 15, residue 6849. -/
theorem bounds_15_6849 : exactInterval 15 6849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6849 : oddCount 6849 15 = 8 ∧ acceleratedOrbit 15 6849 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6849) = 3 ^ 8 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6849.1, data_15_6849.2]

/-- Complete interval computation for depth 15, residue 6850. -/
theorem bounds_15_6850 : exactInterval 15 6850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6850 : oddCount 6850 15 = 7 ∧ acceleratedOrbit 15 6850 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6850) = 3 ^ 7 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6850.1, data_15_6850.2]

/-- Complete interval computation for depth 15, residue 6851. -/
theorem bounds_15_6851 : exactInterval 15 6851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6851 : oddCount 6851 15 = 7 ∧ acceleratedOrbit 15 6851 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6851) = 3 ^ 7 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6851.1, data_15_6851.2]

/-- Complete interval computation for depth 15, residue 6852. -/
theorem bounds_15_6852 : exactInterval 15 6852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6852 : oddCount 6852 15 = 4 ∧ acceleratedOrbit 15 6852 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6852) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6852.1, data_15_6852.2]

/-- Complete interval computation for depth 15, residue 6853. -/
theorem bounds_15_6853 : exactInterval 15 6853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6853 : oddCount 6853 15 = 4 ∧ acceleratedOrbit 15 6853 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6853) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6853.1, data_15_6853.2]

/-- Complete interval computation for depth 15, residue 6854. -/
theorem bounds_15_6854 : exactInterval 15 6854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6854 : oddCount 6854 15 = 4 ∧ acceleratedOrbit 15 6854 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6854) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6854.1, data_15_6854.2]

/-- Complete interval computation for depth 15, residue 6855. -/
theorem bounds_15_6855 : exactInterval 15 6855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6855 : oddCount 6855 15 = 9 ∧ acceleratedOrbit 15 6855 = 4121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6855) = 3 ^ 9 * m + 4121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6855.1, data_15_6855.2]

/-- Complete interval computation for depth 15, residue 6856. -/
theorem bounds_15_6856 : exactInterval 15 6856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6856 : oddCount 6856 15 = 4 ∧ acceleratedOrbit 15 6856 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6856) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6856.1, data_15_6856.2]

/-- Complete interval computation for depth 15, residue 6857. -/
theorem bounds_15_6857 : exactInterval 15 6857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6857 : oddCount 6857 15 = 8 ∧ acceleratedOrbit 15 6857 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6857) = 3 ^ 8 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6857.1, data_15_6857.2]

/-- Complete interval computation for depth 15, residue 6858. -/
theorem bounds_15_6858 : exactInterval 15 6858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6858 : oddCount 6858 15 = 4 ∧ acceleratedOrbit 15 6858 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6858) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6858.1, data_15_6858.2]

/-- Complete interval computation for depth 15, residue 6859. -/
theorem bounds_15_6859 : exactInterval 15 6859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6859 : oddCount 6859 15 = 9 ∧ acceleratedOrbit 15 6859 = 4124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6859) = 3 ^ 9 * m + 4124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6859.1, data_15_6859.2]

/-- Complete interval computation for depth 15, residue 6860. -/
theorem bounds_15_6860 : exactInterval 15 6860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6860 : oddCount 6860 15 = 4 ∧ acceleratedOrbit 15 6860 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6860) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6860.1, data_15_6860.2]

/-- Complete interval computation for depth 15, residue 6861. -/
theorem bounds_15_6861 : exactInterval 15 6861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6861 : oddCount 6861 15 = 4 ∧ acceleratedOrbit 15 6861 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6861) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6861.1, data_15_6861.2]

/-- Complete interval computation for depth 15, residue 6862. -/
theorem bounds_15_6862 : exactInterval 15 6862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6862 : oddCount 6862 15 = 11 ∧ acceleratedOrbit 15 6862 = 37111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6862) = 3 ^ 11 * m + 37111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6862.1, data_15_6862.2]

/-- Complete interval computation for depth 15, residue 6863. -/
theorem bounds_15_6863 : exactInterval 15 6863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6863 : oddCount 6863 15 = 11 ∧ acceleratedOrbit 15 6863 = 37111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6863) = 3 ^ 11 * m + 37111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6863.1, data_15_6863.2]

/-- Complete interval computation for depth 15, residue 6864. -/
theorem bounds_15_6864 : exactInterval 15 6864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6864 : oddCount 6864 15 = 6 ∧ acceleratedOrbit 15 6864 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6864) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6864.1, data_15_6864.2]

/-- Complete interval computation for depth 15, residue 6865. -/
theorem bounds_15_6865 : exactInterval 15 6865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6865 : oddCount 6865 15 = 9 ∧ acceleratedOrbit 15 6865 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6865) = 3 ^ 9 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6865.1, data_15_6865.2]

/-- Complete interval computation for depth 15, residue 6866. -/
theorem bounds_15_6866 : exactInterval 15 6866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6866 : oddCount 6866 15 = 9 ∧ acceleratedOrbit 15 6866 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6866) = 3 ^ 9 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6866.1, data_15_6866.2]

/-- Complete interval computation for depth 15, residue 6867. -/
theorem bounds_15_6867 : exactInterval 15 6867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6867 : oddCount 6867 15 = 9 ∧ acceleratedOrbit 15 6867 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6867) = 3 ^ 9 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6867.1, data_15_6867.2]

/-- Complete interval computation for depth 15, residue 6868. -/
theorem bounds_15_6868 : exactInterval 15 6868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6868 : oddCount 6868 15 = 6 ∧ acceleratedOrbit 15 6868 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6868) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6868.1, data_15_6868.2]

/-- Complete interval computation for depth 15, residue 6869. -/
theorem bounds_15_6869 : exactInterval 15 6869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6869 : oddCount 6869 15 = 6 ∧ acceleratedOrbit 15 6869 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6869) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6869.1, data_15_6869.2]

/-- Complete interval computation for depth 15, residue 6870. -/
theorem bounds_15_6870 : exactInterval 15 6870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6870 : oddCount 6870 15 = 10 ∧ acceleratedOrbit 15 6870 = 12392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6870) = 3 ^ 10 * m + 12392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6870.1, data_15_6870.2]

/-- Complete interval computation for depth 15, residue 6871. -/
theorem bounds_15_6871 : exactInterval 15 6871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6871 : oddCount 6871 15 = 10 ∧ acceleratedOrbit 15 6871 = 12392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6871) = 3 ^ 10 * m + 12392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6871.1, data_15_6871.2]

/-- Complete interval computation for depth 15, residue 6872. -/
theorem bounds_15_6872 : exactInterval 15 6872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6872 : oddCount 6872 15 = 8 ∧ acceleratedOrbit 15 6872 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6872) = 3 ^ 8 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6872.1, data_15_6872.2]

/-- Complete interval computation for depth 15, residue 6873. -/
theorem bounds_15_6873 : exactInterval 15 6873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6873 : oddCount 6873 15 = 4 ∧ acceleratedOrbit 15 6873 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6873) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6873.1, data_15_6873.2]

/-- Complete interval computation for depth 15, residue 6874. -/
theorem bounds_15_6874 : exactInterval 15 6874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6874 : oddCount 6874 15 = 8 ∧ acceleratedOrbit 15 6874 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6874) = 3 ^ 8 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6874.1, data_15_6874.2]

/-- Complete interval computation for depth 15, residue 6875. -/
theorem bounds_15_6875 : exactInterval 15 6875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6875 : oddCount 6875 15 = 12 ∧ acceleratedOrbit 15 6875 = 111536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6875) = 3 ^ 12 * m + 111536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6875.1, data_15_6875.2]

/-- Complete interval computation for depth 15, residue 6876. -/
theorem bounds_15_6876 : exactInterval 15 6876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6876 : oddCount 6876 15 = 8 ∧ acceleratedOrbit 15 6876 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6876) = 3 ^ 8 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6876.1, data_15_6876.2]

/-- Complete interval computation for depth 15, residue 6877. -/
theorem bounds_15_6877 : exactInterval 15 6877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6877 : oddCount 6877 15 = 8 ∧ acceleratedOrbit 15 6877 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6877) = 3 ^ 8 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6877.1, data_15_6877.2]

/-- Complete interval computation for depth 15, residue 6878. -/
theorem bounds_15_6878 : exactInterval 15 6878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6878 : oddCount 6878 15 = 8 ∧ acceleratedOrbit 15 6878 = 1378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6878) = 3 ^ 8 * m + 1378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6878.1, data_15_6878.2]

/-- Complete interval computation for depth 15, residue 6879. -/
theorem bounds_15_6879 : exactInterval 15 6879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6879 : oddCount 6879 15 = 8 ∧ acceleratedOrbit 15 6879 = 1378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6879) = 3 ^ 8 * m + 1378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6879.1, data_15_6879.2]

/-- Complete interval computation for depth 15, residue 6880. -/
theorem bounds_15_6880 : exactInterval 15 6880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6880 : oddCount 6880 15 = 6 ∧ acceleratedOrbit 15 6880 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6880) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6880.1, data_15_6880.2]

end Collatz.Research.PassageAtlas.Batch0210
