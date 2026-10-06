import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0451

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3840. -/
theorem bounds_12_3840 : exactInterval 12 3840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3840 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3840) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3840 : oddCount 3840 12 = 4 ∧ acceleratedOrbit 12 3840 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3840 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3840) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3840.1, data_12_3840.2]

/-- Complete interval computation for depth 12, residue 3841. -/
theorem bounds_12_3841 : exactInterval 12 3841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3841 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3841) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3841 : oddCount 3841 12 = 4 ∧ acceleratedOrbit 12 3841 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3841 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3841) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3841.1, data_12_3841.2]

/-- Complete interval computation for depth 12, residue 3842. -/
theorem bounds_12_3842 : exactInterval 12 3842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3842 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3842) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3842 : oddCount 3842 12 = 6 ∧ acceleratedOrbit 12 3842 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3842 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3842) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3842.1, data_12_3842.2]

/-- Complete interval computation for depth 12, residue 3843. -/
theorem bounds_12_3843 : exactInterval 12 3843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3843 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3843) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3843 : oddCount 3843 12 = 6 ∧ acceleratedOrbit 12 3843 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3843 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3843) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3843.1, data_12_3843.2]

/-- Complete interval computation for depth 12, residue 3844. -/
theorem bounds_12_3844 : exactInterval 12 3844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3844 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3844) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3844 : oddCount 3844 12 = 5 ∧ acceleratedOrbit 12 3844 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3844 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3844) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3844.1, data_12_3844.2]

/-- Complete interval computation for depth 12, residue 3845. -/
theorem bounds_12_3845 : exactInterval 12 3845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3845 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3845) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3845 : oddCount 3845 12 = 5 ∧ acceleratedOrbit 12 3845 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3845 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3845) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3845.1, data_12_3845.2]

/-- Complete interval computation for depth 12, residue 3846. -/
theorem bounds_12_3846 : exactInterval 12 3846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3846 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3846) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3846 : oddCount 3846 12 = 5 ∧ acceleratedOrbit 12 3846 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3846 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3846) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3846.1, data_12_3846.2]

/-- Complete interval computation for depth 12, residue 3847. -/
theorem bounds_12_3847 : exactInterval 12 3847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3847 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3847) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3847 : oddCount 3847 12 = 6 ∧ acceleratedOrbit 12 3847 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3847 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3847) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3847.1, data_12_3847.2]

/-- Complete interval computation for depth 12, residue 3848. -/
theorem bounds_12_3848 : exactInterval 12 3848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3848 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3848) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3848 : oddCount 3848 12 = 6 ∧ acceleratedOrbit 12 3848 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3848 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3848) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3848.1, data_12_3848.2]

/-- Complete interval computation for depth 12, residue 3849. -/
theorem bounds_12_3849 : exactInterval 12 3849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3849 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3849) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3849 : oddCount 3849 12 = 8 ∧ acceleratedOrbit 12 3849 = 6169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3849 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3849) = 3 ^ 8 * m + 6169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3849.1, data_12_3849.2]

/-- Complete interval computation for depth 12, residue 3850. -/
theorem bounds_12_3850 : exactInterval 12 3850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3850 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3850) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3850 : oddCount 3850 12 = 6 ∧ acceleratedOrbit 12 3850 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3850 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3850) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3850.1, data_12_3850.2]

/-- Complete interval computation for depth 12, residue 3851. -/
theorem bounds_12_3851 : exactInterval 12 3851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3851 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3851) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3851 : oddCount 3851 12 = 6 ∧ acceleratedOrbit 12 3851 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3851 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3851) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3851.1, data_12_3851.2]

/-- Complete interval computation for depth 12, residue 3852. -/
theorem bounds_12_3852 : exactInterval 12 3852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3852 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3852) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3852 : oddCount 3852 12 = 6 ∧ acceleratedOrbit 12 3852 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3852 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3852) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3852.1, data_12_3852.2]

/-- Complete interval computation for depth 12, residue 3853. -/
theorem bounds_12_3853 : exactInterval 12 3853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3853 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3853) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3853 : oddCount 3853 12 = 6 ∧ acceleratedOrbit 12 3853 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3853 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3853) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3853.1, data_12_3853.2]

/-- Complete interval computation for depth 12, residue 3854. -/
theorem bounds_12_3854 : exactInterval 12 3854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3854 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3854) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3854 : oddCount 3854 12 = 5 ∧ acceleratedOrbit 12 3854 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3854 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3854) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3854.1, data_12_3854.2]

end Collatz.Research.StoppingAtlas.Batch0451
