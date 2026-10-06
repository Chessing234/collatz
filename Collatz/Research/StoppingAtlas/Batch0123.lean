import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0123

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 849. -/
theorem bounds_11_849 : exactInterval 11 849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_849 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 849) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_849 : oddCount 849 11 = 7 ∧ acceleratedOrbit 11 849 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_849 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 849) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_849.1, data_11_849.2]

/-- Complete interval computation for depth 11, residue 850. -/
theorem bounds_11_850 : exactInterval 11 850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_850 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 850) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_850 : oddCount 850 11 = 7 ∧ acceleratedOrbit 11 850 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_850 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 850) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_850.1, data_11_850.2]

/-- Complete interval computation for depth 11, residue 851. -/
theorem bounds_11_851 : exactInterval 11 851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_851 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 851) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_851 : oddCount 851 11 = 7 ∧ acceleratedOrbit 11 851 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_851 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 851) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_851.1, data_11_851.2]

/-- Complete interval computation for depth 11, residue 852. -/
theorem bounds_11_852 : exactInterval 11 852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_852 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 852) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_852 : oddCount 852 11 = 2 ∧ acceleratedOrbit 11 852 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_852 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 852) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_852.1, data_11_852.2]

/-- Complete interval computation for depth 11, residue 853. -/
theorem bounds_11_853 : exactInterval 11 853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_853 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 853) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_853 : oddCount 853 11 = 2 ∧ acceleratedOrbit 11 853 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_853 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 853) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_853.1, data_11_853.2]

/-- Complete interval computation for depth 11, residue 854. -/
theorem bounds_11_854 : exactInterval 11 854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_854 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 854) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_854 : oddCount 854 11 = 7 ∧ acceleratedOrbit 11 854 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_854 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 854) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_854.1, data_11_854.2]

/-- Complete interval computation for depth 11, residue 855. -/
theorem bounds_11_855 : exactInterval 11 855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_855 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 855) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_855 : oddCount 855 11 = 7 ∧ acceleratedOrbit 11 855 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_855 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 855) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_855.1, data_11_855.2]

/-- Complete interval computation for depth 11, residue 856. -/
theorem bounds_11_856 : exactInterval 11 856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_856 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 856) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_856 : oddCount 856 11 = 5 ∧ acceleratedOrbit 11 856 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_856 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 856) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_856.1, data_11_856.2]

/-- Complete interval computation for depth 11, residue 857. -/
theorem bounds_11_857 : exactInterval 11 857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_857 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 857) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_857 : oddCount 857 11 = 4 ∧ acceleratedOrbit 11 857 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_857 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 857) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_857.1, data_11_857.2]

/-- Complete interval computation for depth 11, residue 858. -/
theorem bounds_11_858 : exactInterval 11 858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_858 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 858) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_858 : oddCount 858 11 = 5 ∧ acceleratedOrbit 11 858 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_858 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 858) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_858.1, data_11_858.2]

/-- Complete interval computation for depth 11, residue 859. -/
theorem bounds_11_859 : exactInterval 11 859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_859 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 859) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_859 : oddCount 859 11 = 7 ∧ acceleratedOrbit 11 859 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_859 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 859) = 3 ^ 7 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_859.1, data_11_859.2]

/-- Complete interval computation for depth 11, residue 860. -/
theorem bounds_11_860 : exactInterval 11 860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_860 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 860) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_860 : oddCount 860 11 = 5 ∧ acceleratedOrbit 11 860 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_860 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 860) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_860.1, data_11_860.2]

/-- Complete interval computation for depth 11, residue 861. -/
theorem bounds_11_861 : exactInterval 11 861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_861 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 861) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_861 : oddCount 861 11 = 5 ∧ acceleratedOrbit 11 861 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_861 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 861) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_861.1, data_11_861.2]

/-- Complete interval computation for depth 11, residue 862. -/
theorem bounds_11_862 : exactInterval 11 862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_862 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 862) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_862 : oddCount 862 11 = 6 ∧ acceleratedOrbit 11 862 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_862 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 862) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_862.1, data_11_862.2]

/-- Complete interval computation for depth 11, residue 863. -/
theorem bounds_11_863 : exactInterval 11 863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_863 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 863) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_863 : oddCount 863 11 = 6 ∧ acceleratedOrbit 11 863 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_863 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 863) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_863.1, data_11_863.2]

/-- Complete interval computation for depth 11, residue 864. -/
theorem bounds_11_864 : exactInterval 11 864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_864 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 864) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_864 : oddCount 864 11 = 5 ∧ acceleratedOrbit 11 864 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_864 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 864) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_864.1, data_11_864.2]

end Collatz.Research.StoppingAtlas.Batch0123
