import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0256

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 844. -/
theorem bounds_12_844 : exactInterval 12 844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_844 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 844) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_844 : oddCount 844 12 = 6 ∧ acceleratedOrbit 12 844 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_844 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 844) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_844.1, data_12_844.2]

/-- Complete interval computation for depth 12, residue 845. -/
theorem bounds_12_845 : exactInterval 12 845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_845 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 845) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_845 : oddCount 845 12 = 6 ∧ acceleratedOrbit 12 845 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_845 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 845) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_845.1, data_12_845.2]

/-- Complete interval computation for depth 12, residue 846. -/
theorem bounds_12_846 : exactInterval 12 846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_846 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 846) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_846 : oddCount 846 12 = 6 ∧ acceleratedOrbit 12 846 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_846 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 846) = 3 ^ 6 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_846.1, data_12_846.2]

/-- Complete interval computation for depth 12, residue 847. -/
theorem bounds_12_847 : exactInterval 12 847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_847 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 847) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_847 : oddCount 847 12 = 6 ∧ acceleratedOrbit 12 847 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_847 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 847) = 3 ^ 6 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_847.1, data_12_847.2]

/-- Complete interval computation for depth 12, residue 848. -/
theorem bounds_12_848 : exactInterval 12 848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_848 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 848) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_848 : oddCount 848 12 = 2 ∧ acceleratedOrbit 12 848 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_848 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 848) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_848.1, data_12_848.2]

/-- Complete interval computation for depth 12, residue 849. -/
theorem bounds_12_849 : exactInterval 12 849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_849 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 849) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_849 : oddCount 849 12 = 8 ∧ acceleratedOrbit 12 849 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_849 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 849) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_849.1, data_12_849.2]

/-- Complete interval computation for depth 12, residue 850. -/
theorem bounds_12_850 : exactInterval 12 850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_850 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 850) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_850 : oddCount 850 12 = 8 ∧ acceleratedOrbit 12 850 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_850 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 850) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_850.1, data_12_850.2]

/-- Complete interval computation for depth 12, residue 851. -/
theorem bounds_12_851 : exactInterval 12 851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_851 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 851) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_851 : oddCount 851 12 = 8 ∧ acceleratedOrbit 12 851 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_851 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 851) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_851.1, data_12_851.2]

/-- Complete interval computation for depth 12, residue 852. -/
theorem bounds_12_852 : exactInterval 12 852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_852 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 852) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_852 : oddCount 852 12 = 2 ∧ acceleratedOrbit 12 852 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_852 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 852) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_852.1, data_12_852.2]

/-- Complete interval computation for depth 12, residue 853. -/
theorem bounds_12_853 : exactInterval 12 853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_853 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 853) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_853 : oddCount 853 12 = 2 ∧ acceleratedOrbit 12 853 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_853 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 853) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_853.1, data_12_853.2]

/-- Complete interval computation for depth 12, residue 854. -/
theorem bounds_12_854 : exactInterval 12 854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_854 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 854) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_854 : oddCount 854 12 = 8 ∧ acceleratedOrbit 12 854 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_854 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 854) = 3 ^ 8 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_854.1, data_12_854.2]

/-- Complete interval computation for depth 12, residue 855. -/
theorem bounds_12_855 : exactInterval 12 855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_855 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 855) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_855 : oddCount 855 12 = 8 ∧ acceleratedOrbit 12 855 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_855 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 855) = 3 ^ 8 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_855.1, data_12_855.2]

/-- Complete interval computation for depth 12, residue 856. -/
theorem bounds_12_856 : exactInterval 12 856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_856 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 856) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_856 : oddCount 856 12 = 6 ∧ acceleratedOrbit 12 856 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_856 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 856) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_856.1, data_12_856.2]

/-- Complete interval computation for depth 12, residue 857. -/
theorem bounds_12_857 : exactInterval 12 857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_857 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 857) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_857 : oddCount 857 12 = 4 ∧ acceleratedOrbit 12 857 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_857 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 857) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_857.1, data_12_857.2]

/-- Complete interval computation for depth 12, residue 858. -/
theorem bounds_12_858 : exactInterval 12 858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_858 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 858) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_858 : oddCount 858 12 = 6 ∧ acceleratedOrbit 12 858 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_858 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 858) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_858.1, data_12_858.2]

/-- Complete interval computation for depth 12, residue 859. -/
theorem bounds_12_859 : exactInterval 12 859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_859 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 859) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_859 : oddCount 859 12 = 8 ∧ acceleratedOrbit 12 859 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_859 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 859) = 3 ^ 8 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_859.1, data_12_859.2]

end Collatz.Research.StoppingAtlas.Batch0256
