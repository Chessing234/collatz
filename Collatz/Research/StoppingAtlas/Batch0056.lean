import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0056

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 844. -/
theorem bounds_10_844 : exactInterval 10 844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_844 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 844) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_844 : oddCount 844 10 = 5 ∧ acceleratedOrbit 10 844 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_844 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 844) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_844.1, data_10_844.2]

/-- Complete interval computation for depth 10, residue 845. -/
theorem bounds_10_845 : exactInterval 10 845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_845 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 845) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_845 : oddCount 845 10 = 5 ∧ acceleratedOrbit 10 845 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_845 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 845) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_845.1, data_10_845.2]

/-- Complete interval computation for depth 10, residue 846. -/
theorem bounds_10_846 : exactInterval 10 846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_846 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 846) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_846 : oddCount 846 10 = 6 ∧ acceleratedOrbit 10 846 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_846 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 846) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_846.1, data_10_846.2]

/-- Complete interval computation for depth 10, residue 847. -/
theorem bounds_10_847 : exactInterval 10 847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_847 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 847) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_847 : oddCount 847 10 = 6 ∧ acceleratedOrbit 10 847 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_847 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 847) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_847.1, data_10_847.2]

/-- Complete interval computation for depth 10, residue 848. -/
theorem bounds_10_848 : exactInterval 10 848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_848 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 848) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_848 : oddCount 848 10 = 2 ∧ acceleratedOrbit 10 848 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_848 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 848) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_848.1, data_10_848.2]

/-- Complete interval computation for depth 10, residue 849. -/
theorem bounds_10_849 : exactInterval 10 849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_849 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 849) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_849 : oddCount 849 10 = 6 ∧ acceleratedOrbit 10 849 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_849 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 849) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_849.1, data_10_849.2]

/-- Complete interval computation for depth 10, residue 850. -/
theorem bounds_10_850 : exactInterval 10 850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_850 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 850) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_850 : oddCount 850 10 = 7 ∧ acceleratedOrbit 10 850 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_850 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 850) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_850.1, data_10_850.2]

/-- Complete interval computation for depth 10, residue 851. -/
theorem bounds_10_851 : exactInterval 10 851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_851 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 851) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_851 : oddCount 851 10 = 7 ∧ acceleratedOrbit 10 851 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_851 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 851) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_851.1, data_10_851.2]

/-- Complete interval computation for depth 10, residue 852. -/
theorem bounds_10_852 : exactInterval 10 852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_852 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 852) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_852 : oddCount 852 10 = 2 ∧ acceleratedOrbit 10 852 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_852 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 852) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_852.1, data_10_852.2]

/-- Complete interval computation for depth 10, residue 853. -/
theorem bounds_10_853 : exactInterval 10 853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_853 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 853) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_853 : oddCount 853 10 = 2 ∧ acceleratedOrbit 10 853 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_853 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 853) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_853.1, data_10_853.2]

/-- Complete interval computation for depth 10, residue 854. -/
theorem bounds_10_854 : exactInterval 10 854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_854 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 854) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_854 : oddCount 854 10 = 6 ∧ acceleratedOrbit 10 854 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_854 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 854) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_854.1, data_10_854.2]

/-- Complete interval computation for depth 10, residue 855. -/
theorem bounds_10_855 : exactInterval 10 855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_855 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 855) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_855 : oddCount 855 10 = 6 ∧ acceleratedOrbit 10 855 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_855 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 855) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_855.1, data_10_855.2]

/-- Complete interval computation for depth 10, residue 856. -/
theorem bounds_10_856 : exactInterval 10 856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_856 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 856) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_856 : oddCount 856 10 = 5 ∧ acceleratedOrbit 10 856 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_856 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 856) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_856.1, data_10_856.2]

/-- Complete interval computation for depth 10, residue 857. -/
theorem bounds_10_857 : exactInterval 10 857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_857 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 857) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_857 : oddCount 857 10 = 4 ∧ acceleratedOrbit 10 857 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_857 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 857) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_857.1, data_10_857.2]

/-- Complete interval computation for depth 10, residue 858. -/
theorem bounds_10_858 : exactInterval 10 858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_858 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 858) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_858 : oddCount 858 10 = 5 ∧ acceleratedOrbit 10 858 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_858 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 858) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_858.1, data_10_858.2]

/-- Complete interval computation for depth 10, residue 859. -/
theorem bounds_10_859 : exactInterval 10 859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_859 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 859) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_859 : oddCount 859 10 = 7 ∧ acceleratedOrbit 10 859 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_859 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 859) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_859.1, data_10_859.2]

end Collatz.Research.StoppingAtlas.Batch0056
