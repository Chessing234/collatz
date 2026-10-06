import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0515

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16842. -/
theorem bounds_15_16842 : exactInterval 15 16842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16842 : oddCount 16842 15 = 5 ∧ acceleratedOrbit 15 16842 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16842) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16842.1, data_15_16842.2]

/-- Complete interval computation for depth 15, residue 16843. -/
theorem bounds_15_16843 : exactInterval 15 16843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16843 : oddCount 16843 15 = 9 ∧ acceleratedOrbit 15 16843 = 10124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16843) = 3 ^ 9 * m + 10124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16843.1, data_15_16843.2]

/-- Complete interval computation for depth 15, residue 16844. -/
theorem bounds_15_16844 : exactInterval 15 16844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16844 : oddCount 16844 15 = 5 ∧ acceleratedOrbit 15 16844 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16844) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16844.1, data_15_16844.2]

/-- Complete interval computation for depth 15, residue 16845. -/
theorem bounds_15_16845 : exactInterval 15 16845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16845 : oddCount 16845 15 = 5 ∧ acceleratedOrbit 15 16845 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16845) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16845.1, data_15_16845.2]

/-- Complete interval computation for depth 15, residue 16846. -/
theorem bounds_15_16846 : exactInterval 15 16846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16846 : oddCount 16846 15 = 8 ∧ acceleratedOrbit 15 16846 = 3374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16846) = 3 ^ 8 * m + 3374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16846.1, data_15_16846.2]

/-- Complete interval computation for depth 15, residue 16847. -/
theorem bounds_15_16847 : exactInterval 15 16847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16847 : oddCount 16847 15 = 8 ∧ acceleratedOrbit 15 16847 = 3374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16847) = 3 ^ 8 * m + 3374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16847.1, data_15_16847.2]

/-- Complete interval computation for depth 15, residue 16848. -/
theorem bounds_15_16848 : exactInterval 15 16848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16848 : oddCount 16848 15 = 6 ∧ acceleratedOrbit 15 16848 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16848) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16848.1, data_15_16848.2]

/-- Complete interval computation for depth 15, residue 16849. -/
theorem bounds_15_16849 : exactInterval 15 16849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16849 : oddCount 16849 15 = 5 ∧ acceleratedOrbit 15 16849 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16849) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16849.1, data_15_16849.2]

/-- Complete interval computation for depth 15, residue 16850. -/
theorem bounds_15_16850 : exactInterval 15 16850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16850 : oddCount 16850 15 = 10 ∧ acceleratedOrbit 15 16850 = 30374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16850) = 3 ^ 10 * m + 30374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16850.1, data_15_16850.2]

/-- Complete interval computation for depth 15, residue 16851. -/
theorem bounds_15_16851 : exactInterval 15 16851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16851 : oddCount 16851 15 = 10 ∧ acceleratedOrbit 15 16851 = 30374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16851) = 3 ^ 10 * m + 30374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16851.1, data_15_16851.2]

/-- Complete interval computation for depth 15, residue 16852. -/
theorem bounds_15_16852 : exactInterval 15 16852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16852 : oddCount 16852 15 = 6 ∧ acceleratedOrbit 15 16852 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16852) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16852.1, data_15_16852.2]

/-- Complete interval computation for depth 15, residue 16853. -/
theorem bounds_15_16853 : exactInterval 15 16853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16853 : oddCount 16853 15 = 6 ∧ acceleratedOrbit 15 16853 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16853) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16853.1, data_15_16853.2]

/-- Complete interval computation for depth 15, residue 16854. -/
theorem bounds_15_16854 : exactInterval 15 16854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16854 : oddCount 16854 15 = 9 ∧ acceleratedOrbit 15 16854 = 10127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16854) = 3 ^ 9 * m + 10127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16854.1, data_15_16854.2]

/-- Complete interval computation for depth 15, residue 16855. -/
theorem bounds_15_16855 : exactInterval 15 16855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16855 : oddCount 16855 15 = 9 ∧ acceleratedOrbit 15 16855 = 10127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16855) = 3 ^ 9 * m + 10127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16855.1, data_15_16855.2]

/-- Complete interval computation for depth 15, residue 16856. -/
theorem bounds_15_16856 : exactInterval 15 16856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16856 : oddCount 16856 15 = 7 ∧ acceleratedOrbit 15 16856 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16856) = 3 ^ 7 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16856.1, data_15_16856.2]

/-- Complete interval computation for depth 15, residue 16857. -/
theorem bounds_15_16857 : exactInterval 15 16857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16857 : oddCount 16857 15 = 7 ∧ acceleratedOrbit 15 16857 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16857) = 3 ^ 7 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16857.1, data_15_16857.2]

/-- Complete interval computation for depth 15, residue 16858. -/
theorem bounds_15_16858 : exactInterval 15 16858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16858 : oddCount 16858 15 = 7 ∧ acceleratedOrbit 15 16858 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16858) = 3 ^ 7 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16858.1, data_15_16858.2]

/-- Complete interval computation for depth 15, residue 16859. -/
theorem bounds_15_16859 : exactInterval 15 16859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16859 : oddCount 16859 15 = 8 ∧ acceleratedOrbit 15 16859 = 3377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16859) = 3 ^ 8 * m + 3377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16859.1, data_15_16859.2]

/-- Complete interval computation for depth 15, residue 16860. -/
theorem bounds_15_16860 : exactInterval 15 16860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16860 : oddCount 16860 15 = 7 ∧ acceleratedOrbit 15 16860 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16860) = 3 ^ 7 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16860.1, data_15_16860.2]

/-- Complete interval computation for depth 15, residue 16861. -/
theorem bounds_15_16861 : exactInterval 15 16861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16861 : oddCount 16861 15 = 7 ∧ acceleratedOrbit 15 16861 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16861) = 3 ^ 7 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16861.1, data_15_16861.2]

/-- Complete interval computation for depth 15, residue 16862. -/
theorem bounds_15_16862 : exactInterval 15 16862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16862 : oddCount 16862 15 = 9 ∧ acceleratedOrbit 15 16862 = 10130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16862) = 3 ^ 9 * m + 10130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16862.1, data_15_16862.2]

/-- Complete interval computation for depth 15, residue 16863. -/
theorem bounds_15_16863 : exactInterval 15 16863 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16863) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16863 : oddCount 16863 15 = 9 ∧ acceleratedOrbit 15 16863 = 10130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16863) = 3 ^ 9 * m + 10130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16863.1, data_15_16863.2]

/-- Complete interval computation for depth 15, residue 16864. -/
theorem bounds_15_16864 : exactInterval 15 16864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16864 : oddCount 16864 15 = 6 ∧ acceleratedOrbit 15 16864 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16864) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16864.1, data_15_16864.2]

/-- Complete interval computation for depth 15, residue 16865. -/
theorem bounds_15_16865 : exactInterval 15 16865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16865 : oddCount 16865 15 = 7 ∧ acceleratedOrbit 15 16865 = 1126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16865) = 3 ^ 7 * m + 1126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16865.1, data_15_16865.2]

/-- Complete interval computation for depth 15, residue 16866. -/
theorem bounds_15_16866 : exactInterval 15 16866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16866 : oddCount 16866 15 = 6 ∧ acceleratedOrbit 15 16866 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16866) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16866.1, data_15_16866.2]

/-- Complete interval computation for depth 15, residue 16867. -/
theorem bounds_15_16867 : exactInterval 15 16867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16867 : oddCount 16867 15 = 6 ∧ acceleratedOrbit 15 16867 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16867) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16867.1, data_15_16867.2]

/-- Complete interval computation for depth 15, residue 16868. -/
theorem bounds_15_16868 : exactInterval 15 16868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16868 : oddCount 16868 15 = 9 ∧ acceleratedOrbit 15 16868 = 10138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16868) = 3 ^ 9 * m + 10138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16868.1, data_15_16868.2]

/-- Complete interval computation for depth 15, residue 16869. -/
theorem bounds_15_16869 : exactInterval 15 16869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16869 : oddCount 16869 15 = 9 ∧ acceleratedOrbit 15 16869 = 10138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16869) = 3 ^ 9 * m + 10138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16869.1, data_15_16869.2]

/-- Complete interval computation for depth 15, residue 16870. -/
theorem bounds_15_16870 : exactInterval 15 16870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16870 : oddCount 16870 15 = 9 ∧ acceleratedOrbit 15 16870 = 10138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16870) = 3 ^ 9 * m + 10138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16870.1, data_15_16870.2]

/-- Complete interval computation for depth 15, residue 16871. -/
theorem bounds_15_16871 : exactInterval 15 16871 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16871) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16871 : oddCount 16871 15 = 9 ∧ acceleratedOrbit 15 16871 = 10135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16871) = 3 ^ 9 * m + 10135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16871.1, data_15_16871.2]

/-- Complete interval computation for depth 15, residue 16872. -/
theorem bounds_15_16872 : exactInterval 15 16872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16872 : oddCount 16872 15 = 6 ∧ acceleratedOrbit 15 16872 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16872) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16872.1, data_15_16872.2]

/-- Complete interval computation for depth 15, residue 16873. -/
theorem bounds_15_16873 : exactInterval 15 16873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16873 : oddCount 16873 15 = 8 ∧ acceleratedOrbit 15 16873 = 3379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16873) = 3 ^ 8 * m + 3379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16873.1, data_15_16873.2]

/-- Complete interval computation for depth 15, residue 16874. -/
theorem bounds_15_16874 : exactInterval 15 16874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16874 : oddCount 16874 15 = 6 ∧ acceleratedOrbit 15 16874 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16874) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16874.1, data_15_16874.2]

end Collatz.Research.PassageAtlas.Batch0515
