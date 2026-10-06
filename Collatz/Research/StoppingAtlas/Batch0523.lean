import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0523

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 849. -/
theorem bounds_13_849 : exactInterval 13 849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_849 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 849) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_849 : oddCount 849 13 = 9 ∧ acceleratedOrbit 13 849 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_849 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 849) = 3 ^ 9 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_849.1, data_13_849.2]

/-- Complete interval computation for depth 13, residue 850. -/
theorem bounds_13_850 : exactInterval 13 850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_850 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 850) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_850 : oddCount 850 13 = 9 ∧ acceleratedOrbit 13 850 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_850 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 850) = 3 ^ 9 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_850.1, data_13_850.2]

/-- Complete interval computation for depth 13, residue 851. -/
theorem bounds_13_851 : exactInterval 13 851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_851 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 851) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_851 : oddCount 851 13 = 9 ∧ acceleratedOrbit 13 851 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_851 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 851) = 3 ^ 9 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_851.1, data_13_851.2]

/-- Complete interval computation for depth 13, residue 852. -/
theorem bounds_13_852 : exactInterval 13 852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_852 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 852) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_852 : oddCount 852 13 = 2 ∧ acceleratedOrbit 13 852 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_852 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 852) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_852.1, data_13_852.2]

/-- Complete interval computation for depth 13, residue 853. -/
theorem bounds_13_853 : exactInterval 13 853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_853 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 853) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_853 : oddCount 853 13 = 2 ∧ acceleratedOrbit 13 853 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_853 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 853) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_853.1, data_13_853.2]

/-- Complete interval computation for depth 13, residue 854. -/
theorem bounds_13_854 : exactInterval 13 854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_854 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 854) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_854 : oddCount 854 13 = 8 ∧ acceleratedOrbit 13 854 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_854 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 854) = 3 ^ 8 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_854.1, data_13_854.2]

/-- Complete interval computation for depth 13, residue 855. -/
theorem bounds_13_855 : exactInterval 13 855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_855 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 855) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_855 : oddCount 855 13 = 8 ∧ acceleratedOrbit 13 855 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_855 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 855) = 3 ^ 8 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_855.1, data_13_855.2]

/-- Complete interval computation for depth 13, residue 856. -/
theorem bounds_13_856 : exactInterval 13 856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_856 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 856) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_856 : oddCount 856 13 = 7 ∧ acceleratedOrbit 13 856 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_856 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 856) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_856.1, data_13_856.2]

/-- Complete interval computation for depth 13, residue 857. -/
theorem bounds_13_857 : exactInterval 13 857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_857 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 857) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_857 : oddCount 857 13 = 5 ∧ acceleratedOrbit 13 857 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_857 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 857) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_857.1, data_13_857.2]

/-- Complete interval computation for depth 13, residue 858. -/
theorem bounds_13_858 : exactInterval 13 858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_858 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 858) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_858 : oddCount 858 13 = 7 ∧ acceleratedOrbit 13 858 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_858 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 858) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_858.1, data_13_858.2]

/-- Complete interval computation for depth 13, residue 859. -/
theorem bounds_13_859 : exactInterval 13 859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_859 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 859) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_859 : oddCount 859 13 = 9 ∧ acceleratedOrbit 13 859 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_859 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 859) = 3 ^ 9 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_859.1, data_13_859.2]

/-- Complete interval computation for depth 13, residue 860. -/
theorem bounds_13_860 : exactInterval 13 860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_860 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 860) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_860 : oddCount 860 13 = 7 ∧ acceleratedOrbit 13 860 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_860 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 860) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_860.1, data_13_860.2]

/-- Complete interval computation for depth 13, residue 861. -/
theorem bounds_13_861 : exactInterval 13 861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_861 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 861) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_861 : oddCount 861 13 = 7 ∧ acceleratedOrbit 13 861 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_861 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 861) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_861.1, data_13_861.2]

/-- Complete interval computation for depth 13, residue 862. -/
theorem bounds_13_862 : exactInterval 13 862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_862 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 862) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_862 : oddCount 862 13 = 6 ∧ acceleratedOrbit 13 862 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_862 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 862) = 3 ^ 6 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_862.1, data_13_862.2]

/-- Complete interval computation for depth 13, residue 863. -/
theorem bounds_13_863 : exactInterval 13 863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_863 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 863) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_863 : oddCount 863 13 = 6 ∧ acceleratedOrbit 13 863 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_863 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 863) = 3 ^ 6 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_863.1, data_13_863.2]

/-- Complete interval computation for depth 13, residue 864. -/
theorem bounds_13_864 : exactInterval 13 864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_864 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 864) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_864 : oddCount 864 13 = 7 ∧ acceleratedOrbit 13 864 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_864 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 864) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_864.1, data_13_864.2]

end Collatz.Research.StoppingAtlas.Batch0523
