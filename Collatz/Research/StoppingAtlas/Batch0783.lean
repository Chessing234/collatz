import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0783

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4843. -/
theorem bounds_13_4843 : exactInterval 13 4843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4843 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4843) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4843 : oddCount 4843 13 = 8 ∧ acceleratedOrbit 13 4843 = 3881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4843 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4843) = 3 ^ 8 * m + 3881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4843.1, data_13_4843.2]

/-- Complete interval computation for depth 13, residue 4844. -/
theorem bounds_13_4844 : exactInterval 13 4844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4844 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4844) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4844 : oddCount 4844 13 = 8 ∧ acceleratedOrbit 13 4844 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4844 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4844) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4844.1, data_13_4844.2]

/-- Complete interval computation for depth 13, residue 4845. -/
theorem bounds_13_4845 : exactInterval 13 4845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4845 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4845) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4845 : oddCount 4845 13 = 8 ∧ acceleratedOrbit 13 4845 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4845 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4845) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4845.1, data_13_4845.2]

/-- Complete interval computation for depth 13, residue 4846. -/
theorem bounds_13_4846 : exactInterval 13 4846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4846 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4846) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4846 : oddCount 4846 13 = 8 ∧ acceleratedOrbit 13 4846 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4846 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4846) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4846.1, data_13_4846.2]

/-- Complete interval computation for depth 13, residue 4847. -/
theorem bounds_13_4847 : exactInterval 13 4847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4847 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4847) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4847 : oddCount 4847 13 = 11 ∧ acceleratedOrbit 13 4847 = 104840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4847 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4847) = 3 ^ 11 * m + 104840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4847.1, data_13_4847.2]

/-- Complete interval computation for depth 13, residue 4848. -/
theorem bounds_13_4848 : exactInterval 13 4848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4848 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4848) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4848 : oddCount 4848 13 = 6 ∧ acceleratedOrbit 13 4848 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4848 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4848) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4848.1, data_13_4848.2]

/-- Complete interval computation for depth 13, residue 4849. -/
theorem bounds_13_4849 : exactInterval 13 4849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4849 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4849) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4849 : oddCount 4849 13 = 3 ∧ acceleratedOrbit 13 4849 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4849 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4849) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4849.1, data_13_4849.2]

/-- Complete interval computation for depth 13, residue 4850. -/
theorem bounds_13_4850 : exactInterval 13 4850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4850 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4850) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4850 : oddCount 4850 13 = 10 ∧ acceleratedOrbit 13 4850 = 34991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4850 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4850) = 3 ^ 10 * m + 34991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4850.1, data_13_4850.2]

/-- Complete interval computation for depth 13, residue 4851. -/
theorem bounds_13_4851 : exactInterval 13 4851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4851 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4851) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4851 : oddCount 4851 13 = 10 ∧ acceleratedOrbit 13 4851 = 34991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4851 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4851) = 3 ^ 10 * m + 34991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4851.1, data_13_4851.2]

/-- Complete interval computation for depth 13, residue 4852. -/
theorem bounds_13_4852 : exactInterval 13 4852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4852 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4852) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4852 : oddCount 4852 13 = 6 ∧ acceleratedOrbit 13 4852 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4852 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4852) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4852.1, data_13_4852.2]

/-- Complete interval computation for depth 13, residue 4853. -/
theorem bounds_13_4853 : exactInterval 13 4853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4853 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4853) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4853 : oddCount 4853 13 = 6 ∧ acceleratedOrbit 13 4853 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4853 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4853) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4853.1, data_13_4853.2]

/-- Complete interval computation for depth 13, residue 4854. -/
theorem bounds_13_4854 : exactInterval 13 4854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4854 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4854) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4854 : oddCount 4854 13 = 7 ∧ acceleratedOrbit 13 4854 = 1297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4854 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4854) = 3 ^ 7 * m + 1297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4854.1, data_13_4854.2]

/-- Complete interval computation for depth 13, residue 4855. -/
theorem bounds_13_4855 : exactInterval 13 4855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4855 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4855) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4855 : oddCount 4855 13 = 7 ∧ acceleratedOrbit 13 4855 = 1297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4855 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4855) = 3 ^ 7 * m + 1297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4855.1, data_13_4855.2]

/-- Complete interval computation for depth 13, residue 4856. -/
theorem bounds_13_4856 : exactInterval 13 4856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4856 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4856) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4856 : oddCount 4856 13 = 6 ∧ acceleratedOrbit 13 4856 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4856 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4856) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4856.1, data_13_4856.2]

/-- Complete interval computation for depth 13, residue 4857. -/
theorem bounds_13_4857 : exactInterval 13 4857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4857 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4857) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4857 : oddCount 4857 13 = 7 ∧ acceleratedOrbit 13 4857 = 1298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4857 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4857) = 3 ^ 7 * m + 1298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4857.1, data_13_4857.2]

end Collatz.Research.StoppingAtlas.Batch0783
