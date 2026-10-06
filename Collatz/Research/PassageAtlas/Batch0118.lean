import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0118

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3833. -/
theorem bounds_15_3833 : exactInterval 15 3833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3833 : oddCount 3833 15 = 8 ∧ acceleratedOrbit 15 3833 = 769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3833) = 3 ^ 8 * m + 769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3833.1, data_15_3833.2]

/-- Complete interval computation for depth 15, residue 3834. -/
theorem bounds_15_3834 : exactInterval 15 3834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3834 : oddCount 3834 15 = 9 ∧ acceleratedOrbit 15 3834 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3834) = 3 ^ 9 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3834.1, data_15_3834.2]

/-- Complete interval computation for depth 15, residue 3835. -/
theorem bounds_15_3835 : exactInterval 15 3835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3835 : oddCount 3835 15 = 9 ∧ acceleratedOrbit 15 3835 = 2305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3835) = 3 ^ 9 * m + 2305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3835.1, data_15_3835.2]

/-- Complete interval computation for depth 15, residue 3836. -/
theorem bounds_15_3836 : exactInterval 15 3836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3836 : oddCount 3836 15 = 11 ∧ acceleratedOrbit 15 3836 = 20762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3836) = 3 ^ 11 * m + 20762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3836.1, data_15_3836.2]

/-- Complete interval computation for depth 15, residue 3837. -/
theorem bounds_15_3837 : exactInterval 15 3837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3837 : oddCount 3837 15 = 11 ∧ acceleratedOrbit 15 3837 = 20762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3837) = 3 ^ 11 * m + 20762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3837.1, data_15_3837.2]

/-- Complete interval computation for depth 15, residue 3838. -/
theorem bounds_15_3838 : exactInterval 15 3838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3838 : oddCount 3838 15 = 11 ∧ acceleratedOrbit 15 3838 = 20762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3838) = 3 ^ 11 * m + 20762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3838.1, data_15_3838.2]

/-- Complete interval computation for depth 15, residue 3839. -/
theorem bounds_15_3839 : exactInterval 15 3839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3839 : oddCount 3839 15 = 12 ∧ acceleratedOrbit 15 3839 = 62279 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3839) = 3 ^ 12 * m + 62279 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3839.1, data_15_3839.2]

/-- Complete interval computation for depth 15, residue 3840. -/
theorem bounds_15_3840 : exactInterval 15 3840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3840 : oddCount 3840 15 = 4 ∧ acceleratedOrbit 15 3840 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3840) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3840.1, data_15_3840.2]

/-- Complete interval computation for depth 15, residue 3841. -/
theorem bounds_15_3841 : exactInterval 15 3841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3841 : oddCount 3841 15 = 5 ∧ acceleratedOrbit 15 3841 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3841) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3841.1, data_15_3841.2]

/-- Complete interval computation for depth 15, residue 3842. -/
theorem bounds_15_3842 : exactInterval 15 3842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3842 : oddCount 3842 15 = 7 ∧ acceleratedOrbit 15 3842 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3842) = 3 ^ 7 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3842.1, data_15_3842.2]

/-- Complete interval computation for depth 15, residue 3843. -/
theorem bounds_15_3843 : exactInterval 15 3843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3843 : oddCount 3843 15 = 7 ∧ acceleratedOrbit 15 3843 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3843) = 3 ^ 7 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3843.1, data_15_3843.2]

/-- Complete interval computation for depth 15, residue 3844. -/
theorem bounds_15_3844 : exactInterval 15 3844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3844 : oddCount 3844 15 = 6 ∧ acceleratedOrbit 15 3844 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3844) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3844.1, data_15_3844.2]

/-- Complete interval computation for depth 15, residue 3845. -/
theorem bounds_15_3845 : exactInterval 15 3845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3845 : oddCount 3845 15 = 6 ∧ acceleratedOrbit 15 3845 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3845) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3845.1, data_15_3845.2]

/-- Complete interval computation for depth 15, residue 3846. -/
theorem bounds_15_3846 : exactInterval 15 3846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3846 : oddCount 3846 15 = 6 ∧ acceleratedOrbit 15 3846 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3846) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3846.1, data_15_3846.2]

/-- Complete interval computation for depth 15, residue 3847. -/
theorem bounds_15_3847 : exactInterval 15 3847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3847 : oddCount 3847 15 = 7 ∧ acceleratedOrbit 15 3847 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3847) = 3 ^ 7 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3847.1, data_15_3847.2]

/-- Complete interval computation for depth 15, residue 3848. -/
theorem bounds_15_3848 : exactInterval 15 3848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3848 : oddCount 3848 15 = 6 ∧ acceleratedOrbit 15 3848 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3848) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3848.1, data_15_3848.2]

/-- Complete interval computation for depth 15, residue 3849. -/
theorem bounds_15_3849 : exactInterval 15 3849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3849 : oddCount 3849 15 = 10 ∧ acceleratedOrbit 15 3849 = 6941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3849) = 3 ^ 10 * m + 6941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3849.1, data_15_3849.2]

/-- Complete interval computation for depth 15, residue 3850. -/
theorem bounds_15_3850 : exactInterval 15 3850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3850 : oddCount 3850 15 = 6 ∧ acceleratedOrbit 15 3850 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3850) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3850.1, data_15_3850.2]

/-- Complete interval computation for depth 15, residue 3851. -/
theorem bounds_15_3851 : exactInterval 15 3851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3851 : oddCount 3851 15 = 8 ∧ acceleratedOrbit 15 3851 = 773 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3851) = 3 ^ 8 * m + 773 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3851.1, data_15_3851.2]

/-- Complete interval computation for depth 15, residue 3852. -/
theorem bounds_15_3852 : exactInterval 15 3852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3852 : oddCount 3852 15 = 6 ∧ acceleratedOrbit 15 3852 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3852) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3852.1, data_15_3852.2]

/-- Complete interval computation for depth 15, residue 3853. -/
theorem bounds_15_3853 : exactInterval 15 3853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3853 : oddCount 3853 15 = 6 ∧ acceleratedOrbit 15 3853 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3853) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3853.1, data_15_3853.2]

/-- Complete interval computation for depth 15, residue 3854. -/
theorem bounds_15_3854 : exactInterval 15 3854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3854 : oddCount 3854 15 = 6 ∧ acceleratedOrbit 15 3854 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3854) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3854.1, data_15_3854.2]

/-- Complete interval computation for depth 15, residue 3855. -/
theorem bounds_15_3855 : exactInterval 15 3855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3855 : oddCount 3855 15 = 6 ∧ acceleratedOrbit 15 3855 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3855) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3855.1, data_15_3855.2]

/-- Complete interval computation for depth 15, residue 3856. -/
theorem bounds_15_3856 : exactInterval 15 3856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3856 : oddCount 3856 15 = 4 ∧ acceleratedOrbit 15 3856 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3856) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3856.1, data_15_3856.2]

/-- Complete interval computation for depth 15, residue 3857. -/
theorem bounds_15_3857 : exactInterval 15 3857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3857 : oddCount 3857 15 = 6 ∧ acceleratedOrbit 15 3857 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3857) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3857.1, data_15_3857.2]

/-- Complete interval computation for depth 15, residue 3858. -/
theorem bounds_15_3858 : exactInterval 15 3858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3858 : oddCount 3858 15 = 9 ∧ acceleratedOrbit 15 3858 = 2321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3858) = 3 ^ 9 * m + 2321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3858.1, data_15_3858.2]

/-- Complete interval computation for depth 15, residue 3859. -/
theorem bounds_15_3859 : exactInterval 15 3859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3859 : oddCount 3859 15 = 9 ∧ acceleratedOrbit 15 3859 = 2321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3859) = 3 ^ 9 * m + 2321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3859.1, data_15_3859.2]

/-- Complete interval computation for depth 15, residue 3860. -/
theorem bounds_15_3860 : exactInterval 15 3860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3860 : oddCount 3860 15 = 4 ∧ acceleratedOrbit 15 3860 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3860) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3860.1, data_15_3860.2]

/-- Complete interval computation for depth 15, residue 3861. -/
theorem bounds_15_3861 : exactInterval 15 3861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3861 : oddCount 3861 15 = 4 ∧ acceleratedOrbit 15 3861 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3861) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3861.1, data_15_3861.2]

/-- Complete interval computation for depth 15, residue 3862. -/
theorem bounds_15_3862 : exactInterval 15 3862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3862 : oddCount 3862 15 = 9 ∧ acceleratedOrbit 15 3862 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3862) = 3 ^ 9 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3862.1, data_15_3862.2]

/-- Complete interval computation for depth 15, residue 3863. -/
theorem bounds_15_3863 : exactInterval 15 3863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3863 : oddCount 3863 15 = 9 ∧ acceleratedOrbit 15 3863 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3863) = 3 ^ 9 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3863.1, data_15_3863.2]

/-- Complete interval computation for depth 15, residue 3864. -/
theorem bounds_15_3864 : exactInterval 15 3864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3864 : oddCount 3864 15 = 4 ∧ acceleratedOrbit 15 3864 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3864) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3864.1, data_15_3864.2]

/-- Complete interval computation for depth 15, residue 3865. -/
theorem bounds_15_3865 : exactInterval 15 3865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3865 : oddCount 3865 15 = 9 ∧ acceleratedOrbit 15 3865 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3865) = 3 ^ 9 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3865.1, data_15_3865.2]

end Collatz.Research.PassageAtlas.Batch0118
