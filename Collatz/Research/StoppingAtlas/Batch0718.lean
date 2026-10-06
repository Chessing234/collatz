import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0718

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3845. -/
theorem bounds_13_3845 : exactInterval 13 3845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3845 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3845) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3845 : oddCount 3845 13 = 6 ∧ acceleratedOrbit 13 3845 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3845 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3845) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3845.1, data_13_3845.2]

/-- Complete interval computation for depth 13, residue 3846. -/
theorem bounds_13_3846 : exactInterval 13 3846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3846 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3846) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3846 : oddCount 3846 13 = 6 ∧ acceleratedOrbit 13 3846 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3846 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3846) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3846.1, data_13_3846.2]

/-- Complete interval computation for depth 13, residue 3847. -/
theorem bounds_13_3847 : exactInterval 13 3847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3847 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3847) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3847 : oddCount 3847 13 = 7 ∧ acceleratedOrbit 13 3847 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3847 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3847) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3847.1, data_13_3847.2]

/-- Complete interval computation for depth 13, residue 3848. -/
theorem bounds_13_3848 : exactInterval 13 3848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3848 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3848) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3848 : oddCount 3848 13 = 6 ∧ acceleratedOrbit 13 3848 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3848 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3848) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3848.1, data_13_3848.2]

/-- Complete interval computation for depth 13, residue 3849. -/
theorem bounds_13_3849 : exactInterval 13 3849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3849 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3849) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3849 : oddCount 3849 13 = 9 ∧ acceleratedOrbit 13 3849 = 9254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3849 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3849) = 3 ^ 9 * m + 9254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3849.1, data_13_3849.2]

/-- Complete interval computation for depth 13, residue 3850. -/
theorem bounds_13_3850 : exactInterval 13 3850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3850 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3850) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3850 : oddCount 3850 13 = 6 ∧ acceleratedOrbit 13 3850 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3850 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3850) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3850.1, data_13_3850.2]

/-- Complete interval computation for depth 13, residue 3851. -/
theorem bounds_13_3851 : exactInterval 13 3851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3851 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3851) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3851 : oddCount 3851 13 = 6 ∧ acceleratedOrbit 13 3851 = 343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3851 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3851) = 3 ^ 6 * m + 343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3851.1, data_13_3851.2]

/-- Complete interval computation for depth 13, residue 3852. -/
theorem bounds_13_3852 : exactInterval 13 3852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3852 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3852) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3852 : oddCount 3852 13 = 6 ∧ acceleratedOrbit 13 3852 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3852 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3852) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3852.1, data_13_3852.2]

/-- Complete interval computation for depth 13, residue 3853. -/
theorem bounds_13_3853 : exactInterval 13 3853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3853 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3853) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3853 : oddCount 3853 13 = 6 ∧ acceleratedOrbit 13 3853 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3853 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3853) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3853.1, data_13_3853.2]

/-- Complete interval computation for depth 13, residue 3854. -/
theorem bounds_13_3854 : exactInterval 13 3854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3854 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3854) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3854 : oddCount 3854 13 = 6 ∧ acceleratedOrbit 13 3854 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3854 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3854) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3854.1, data_13_3854.2]

/-- Complete interval computation for depth 13, residue 3855. -/
theorem bounds_13_3855 : exactInterval 13 3855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3855 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3855) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3855 : oddCount 3855 13 = 6 ∧ acceleratedOrbit 13 3855 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3855 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3855) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3855.1, data_13_3855.2]

/-- Complete interval computation for depth 13, residue 3856. -/
theorem bounds_13_3856 : exactInterval 13 3856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3856 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3856) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3856 : oddCount 3856 13 = 3 ∧ acceleratedOrbit 13 3856 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3856 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3856) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3856.1, data_13_3856.2]

/-- Complete interval computation for depth 13, residue 3857. -/
theorem bounds_13_3857 : exactInterval 13 3857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3857 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3857) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3857 : oddCount 3857 13 = 6 ∧ acceleratedOrbit 13 3857 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3857 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3857) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3857.1, data_13_3857.2]

/-- Complete interval computation for depth 13, residue 3858. -/
theorem bounds_13_3858 : exactInterval 13 3858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3858 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3858) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3858 : oddCount 3858 13 = 7 ∧ acceleratedOrbit 13 3858 = 1031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3858 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3858) = 3 ^ 7 * m + 1031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3858.1, data_13_3858.2]

/-- Complete interval computation for depth 13, residue 3859. -/
theorem bounds_13_3859 : exactInterval 13 3859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3859 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3859) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3859 : oddCount 3859 13 = 7 ∧ acceleratedOrbit 13 3859 = 1031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3859 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3859) = 3 ^ 7 * m + 1031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3859.1, data_13_3859.2]

end Collatz.Research.StoppingAtlas.Batch0718
