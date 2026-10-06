import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0973

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31850. -/
theorem bounds_15_31850 : exactInterval 15 31850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31850 : oddCount 31850 15 = 4 ∧ acceleratedOrbit 15 31850 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31850) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31850.1, data_15_31850.2]

/-- Complete interval computation for depth 15, residue 31851. -/
theorem bounds_15_31851 : exactInterval 15 31851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31851 : oddCount 31851 15 = 11 ∧ acceleratedOrbit 15 31851 = 172205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31851) = 3 ^ 11 * m + 172205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31851.1, data_15_31851.2]

/-- Complete interval computation for depth 15, residue 31852. -/
theorem bounds_15_31852 : exactInterval 15 31852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31852 : oddCount 31852 15 = 11 ∧ acceleratedOrbit 15 31852 = 172226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31852) = 3 ^ 11 * m + 172226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31852.1, data_15_31852.2]

/-- Complete interval computation for depth 15, residue 31853. -/
theorem bounds_15_31853 : exactInterval 15 31853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31853 : oddCount 31853 15 = 11 ∧ acceleratedOrbit 15 31853 = 172226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31853) = 3 ^ 11 * m + 172226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31853.1, data_15_31853.2]

/-- Complete interval computation for depth 15, residue 31854. -/
theorem bounds_15_31854 : exactInterval 15 31854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31854 : oddCount 31854 15 = 11 ∧ acceleratedOrbit 15 31854 = 172226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31854) = 3 ^ 11 * m + 172226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31854.1, data_15_31854.2]

/-- Complete interval computation for depth 15, residue 31855. -/
theorem bounds_15_31855 : exactInterval 15 31855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31855 : oddCount 31855 15 = 11 ∧ acceleratedOrbit 15 31855 = 172219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31855) = 3 ^ 11 * m + 172219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31855.1, data_15_31855.2]

/-- Complete interval computation for depth 15, residue 31856. -/
theorem bounds_15_31856 : exactInterval 15 31856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31856 : oddCount 31856 15 = 7 ∧ acceleratedOrbit 15 31856 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31856) = 3 ^ 7 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31856.1, data_15_31856.2]

/-- Complete interval computation for depth 15, residue 31857. -/
theorem bounds_15_31857 : exactInterval 15 31857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31857 : oddCount 31857 15 = 4 ∧ acceleratedOrbit 15 31857 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31857) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31857.1, data_15_31857.2]

/-- Complete interval computation for depth 15, residue 31858. -/
theorem bounds_15_31858 : exactInterval 15 31858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31858 : oddCount 31858 15 = 9 ∧ acceleratedOrbit 15 31858 = 19142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31858) = 3 ^ 9 * m + 19142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31858.1, data_15_31858.2]

/-- Complete interval computation for depth 15, residue 31859. -/
theorem bounds_15_31859 : exactInterval 15 31859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31859 : oddCount 31859 15 = 9 ∧ acceleratedOrbit 15 31859 = 19142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31859) = 3 ^ 9 * m + 19142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31859.1, data_15_31859.2]

/-- Complete interval computation for depth 15, residue 31860. -/
theorem bounds_15_31860 : exactInterval 15 31860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31860 : oddCount 31860 15 = 7 ∧ acceleratedOrbit 15 31860 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31860) = 3 ^ 7 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31860.1, data_15_31860.2]

/-- Complete interval computation for depth 15, residue 31861. -/
theorem bounds_15_31861 : exactInterval 15 31861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31861 : oddCount 31861 15 = 7 ∧ acceleratedOrbit 15 31861 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31861) = 3 ^ 7 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31861.1, data_15_31861.2]

/-- Complete interval computation for depth 15, residue 31862. -/
theorem bounds_15_31862 : exactInterval 15 31862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31862 : oddCount 31862 15 = 6 ∧ acceleratedOrbit 15 31862 = 709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31862) = 3 ^ 6 * m + 709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31862.1, data_15_31862.2]

/-- Complete interval computation for depth 15, residue 31863. -/
theorem bounds_15_31863 : exactInterval 15 31863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31863 : oddCount 31863 15 = 6 ∧ acceleratedOrbit 15 31863 = 709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31863) = 3 ^ 6 * m + 709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31863.1, data_15_31863.2]

/-- Complete interval computation for depth 15, residue 31864. -/
theorem bounds_15_31864 : exactInterval 15 31864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31864 : oddCount 31864 15 = 7 ∧ acceleratedOrbit 15 31864 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31864) = 3 ^ 7 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31864.1, data_15_31864.2]

/-- Complete interval computation for depth 15, residue 31865. -/
theorem bounds_15_31865 : exactInterval 15 31865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31865 : oddCount 31865 15 = 10 ∧ acceleratedOrbit 15 31865 = 57428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31865) = 3 ^ 10 * m + 57428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31865.1, data_15_31865.2]

/-- Complete interval computation for depth 15, residue 31866. -/
theorem bounds_15_31866 : exactInterval 15 31866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31866 : oddCount 31866 15 = 7 ∧ acceleratedOrbit 15 31866 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31866) = 3 ^ 7 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31866.1, data_15_31866.2]

/-- Complete interval computation for depth 15, residue 31867. -/
theorem bounds_15_31867 : exactInterval 15 31867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31867 : oddCount 31867 15 = 6 ∧ acceleratedOrbit 15 31867 = 709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31867) = 3 ^ 6 * m + 709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31867.1, data_15_31867.2]

/-- Complete interval computation for depth 15, residue 31868. -/
theorem bounds_15_31868 : exactInterval 15 31868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31868 : oddCount 31868 15 = 8 ∧ acceleratedOrbit 15 31868 = 6382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31868) = 3 ^ 8 * m + 6382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31868.1, data_15_31868.2]

/-- Complete interval computation for depth 15, residue 31869. -/
theorem bounds_15_31869 : exactInterval 15 31869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31869 : oddCount 31869 15 = 8 ∧ acceleratedOrbit 15 31869 = 6382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31869) = 3 ^ 8 * m + 6382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31869.1, data_15_31869.2]

/-- Complete interval computation for depth 15, residue 31870. -/
theorem bounds_15_31870 : exactInterval 15 31870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31870 : oddCount 31870 15 = 8 ∧ acceleratedOrbit 15 31870 = 6382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31870) = 3 ^ 8 * m + 6382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31870.1, data_15_31870.2]

/-- Complete interval computation for depth 15, residue 31871. -/
theorem bounds_15_31871 : exactInterval 15 31871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31871 : oddCount 31871 15 = 11 ∧ acceleratedOrbit 15 31871 = 172304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31871) = 3 ^ 11 * m + 172304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31871.1, data_15_31871.2]

/-- Complete interval computation for depth 15, residue 31872. -/
theorem bounds_15_31872 : exactInterval 15 31872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31872 : oddCount 31872 15 = 5 ∧ acceleratedOrbit 15 31872 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31872) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31872.1, data_15_31872.2]

/-- Complete interval computation for depth 15, residue 31873. -/
theorem bounds_15_31873 : exactInterval 15 31873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31873 : oddCount 31873 15 = 8 ∧ acceleratedOrbit 15 31873 = 6383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31873) = 3 ^ 8 * m + 6383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31873.1, data_15_31873.2]

/-- Complete interval computation for depth 15, residue 31874. -/
theorem bounds_15_31874 : exactInterval 15 31874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31874 : oddCount 31874 15 = 6 ∧ acceleratedOrbit 15 31874 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31874) = 3 ^ 6 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31874.1, data_15_31874.2]

/-- Complete interval computation for depth 15, residue 31875. -/
theorem bounds_15_31875 : exactInterval 15 31875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31875 : oddCount 31875 15 = 6 ∧ acceleratedOrbit 15 31875 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31875) = 3 ^ 6 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31875.1, data_15_31875.2]

/-- Complete interval computation for depth 15, residue 31876. -/
theorem bounds_15_31876 : exactInterval 15 31876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31876 : oddCount 31876 15 = 6 ∧ acceleratedOrbit 15 31876 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31876) = 3 ^ 6 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31876.1, data_15_31876.2]

/-- Complete interval computation for depth 15, residue 31877. -/
theorem bounds_15_31877 : exactInterval 15 31877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31877 : oddCount 31877 15 = 6 ∧ acceleratedOrbit 15 31877 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31877) = 3 ^ 6 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31877.1, data_15_31877.2]

/-- Complete interval computation for depth 15, residue 31878. -/
theorem bounds_15_31878 : exactInterval 15 31878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31878 : oddCount 31878 15 = 6 ∧ acceleratedOrbit 15 31878 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31878) = 3 ^ 6 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31878.1, data_15_31878.2]

/-- Complete interval computation for depth 15, residue 31879. -/
theorem bounds_15_31879 : exactInterval 15 31879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31879 : oddCount 31879 15 = 10 ∧ acceleratedOrbit 15 31879 = 57455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31879) = 3 ^ 10 * m + 57455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31879.1, data_15_31879.2]

/-- Complete interval computation for depth 15, residue 31880. -/
theorem bounds_15_31880 : exactInterval 15 31880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31880 : oddCount 31880 15 = 7 ∧ acceleratedOrbit 15 31880 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31880) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31880.1, data_15_31880.2]

/-- Complete interval computation for depth 15, residue 31881. -/
theorem bounds_15_31881 : exactInterval 15 31881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31881 : oddCount 31881 15 = 11 ∧ acceleratedOrbit 15 31881 = 172363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31881) = 3 ^ 11 * m + 172363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31881.1, data_15_31881.2]

/-- Complete interval computation for depth 15, residue 31882. -/
theorem bounds_15_31882 : exactInterval 15 31882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31882 : oddCount 31882 15 = 7 ∧ acceleratedOrbit 15 31882 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31882) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31882.1, data_15_31882.2]

end Collatz.Research.PassageAtlas.Batch0973
