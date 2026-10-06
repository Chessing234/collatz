import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0393

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12845. -/
theorem bounds_15_12845 : exactInterval 15 12845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12845 : oddCount 12845 15 = 6 ∧ acceleratedOrbit 15 12845 = 286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12845) = 3 ^ 6 * m + 286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12845.1, data_15_12845.2]

/-- Complete interval computation for depth 15, residue 12846. -/
theorem bounds_15_12846 : exactInterval 15 12846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12846 : oddCount 12846 15 = 6 ∧ acceleratedOrbit 15 12846 = 286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12846) = 3 ^ 6 * m + 286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12846.1, data_15_12846.2]

/-- Complete interval computation for depth 15, residue 12847. -/
theorem bounds_15_12847 : exactInterval 15 12847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12847 : oddCount 12847 15 = 11 ∧ acceleratedOrbit 15 12847 = 69461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12847) = 3 ^ 11 * m + 69461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12847.1, data_15_12847.2]

/-- Complete interval computation for depth 15, residue 12848. -/
theorem bounds_15_12848 : exactInterval 15 12848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12848 : oddCount 12848 15 = 4 ∧ acceleratedOrbit 15 12848 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12848) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12848.1, data_15_12848.2]

/-- Complete interval computation for depth 15, residue 12849. -/
theorem bounds_15_12849 : exactInterval 15 12849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12849 : oddCount 12849 15 = 6 ∧ acceleratedOrbit 15 12849 = 286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12849) = 3 ^ 6 * m + 286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12849.1, data_15_12849.2]

/-- Complete interval computation for depth 15, residue 12850. -/
theorem bounds_15_12850 : exactInterval 15 12850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12850 : oddCount 12850 15 = 6 ∧ acceleratedOrbit 15 12850 = 286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12850) = 3 ^ 6 * m + 286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12850.1, data_15_12850.2]

/-- Complete interval computation for depth 15, residue 12851. -/
theorem bounds_15_12851 : exactInterval 15 12851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12851 : oddCount 12851 15 = 6 ∧ acceleratedOrbit 15 12851 = 286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12851) = 3 ^ 6 * m + 286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12851.1, data_15_12851.2]

/-- Complete interval computation for depth 15, residue 12852. -/
theorem bounds_15_12852 : exactInterval 15 12852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12852 : oddCount 12852 15 = 4 ∧ acceleratedOrbit 15 12852 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12852) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12852.1, data_15_12852.2]

/-- Complete interval computation for depth 15, residue 12853. -/
theorem bounds_15_12853 : exactInterval 15 12853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12853 : oddCount 12853 15 = 4 ∧ acceleratedOrbit 15 12853 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12853) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12853.1, data_15_12853.2]

/-- Complete interval computation for depth 15, residue 12854. -/
theorem bounds_15_12854 : exactInterval 15 12854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12854 : oddCount 12854 15 = 9 ∧ acceleratedOrbit 15 12854 = 7723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12854) = 3 ^ 9 * m + 7723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12854.1, data_15_12854.2]

/-- Complete interval computation for depth 15, residue 12855. -/
theorem bounds_15_12855 : exactInterval 15 12855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12855 : oddCount 12855 15 = 9 ∧ acceleratedOrbit 15 12855 = 7723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12855) = 3 ^ 9 * m + 7723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12855.1, data_15_12855.2]

/-- Complete interval computation for depth 15, residue 12856. -/
theorem bounds_15_12856 : exactInterval 15 12856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12856 : oddCount 12856 15 = 7 ∧ acceleratedOrbit 15 12856 = 859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12856) = 3 ^ 7 * m + 859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12856.1, data_15_12856.2]

/-- Complete interval computation for depth 15, residue 12857. -/
theorem bounds_15_12857 : exactInterval 15 12857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12857 : oddCount 12857 15 = 8 ∧ acceleratedOrbit 15 12857 = 2575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12857) = 3 ^ 8 * m + 2575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12857.1, data_15_12857.2]

/-- Complete interval computation for depth 15, residue 12858. -/
theorem bounds_15_12858 : exactInterval 15 12858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12858 : oddCount 12858 15 = 7 ∧ acceleratedOrbit 15 12858 = 859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12858) = 3 ^ 7 * m + 859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12858.1, data_15_12858.2]

/-- Complete interval computation for depth 15, residue 12859. -/
theorem bounds_15_12859 : exactInterval 15 12859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12859 : oddCount 12859 15 = 7 ∧ acceleratedOrbit 15 12859 = 859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12859) = 3 ^ 7 * m + 859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12859.1, data_15_12859.2]

/-- Complete interval computation for depth 15, residue 12860. -/
theorem bounds_15_12860 : exactInterval 15 12860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12860 : oddCount 12860 15 = 7 ∧ acceleratedOrbit 15 12860 = 859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12860) = 3 ^ 7 * m + 859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12860.1, data_15_12860.2]

/-- Complete interval computation for depth 15, residue 12861. -/
theorem bounds_15_12861 : exactInterval 15 12861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12861 : oddCount 12861 15 = 7 ∧ acceleratedOrbit 15 12861 = 859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12861) = 3 ^ 7 * m + 859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12861.1, data_15_12861.2]

/-- Complete interval computation for depth 15, residue 12862. -/
theorem bounds_15_12862 : exactInterval 15 12862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12862 : oddCount 12862 15 = 8 ∧ acceleratedOrbit 15 12862 = 2576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12862) = 3 ^ 8 * m + 2576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12862.1, data_15_12862.2]

/-- Complete interval computation for depth 15, residue 12863. -/
theorem bounds_15_12863 : exactInterval 15 12863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12863 : oddCount 12863 15 = 8 ∧ acceleratedOrbit 15 12863 = 2576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12863) = 3 ^ 8 * m + 2576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12863.1, data_15_12863.2]

/-- Complete interval computation for depth 15, residue 12864. -/
theorem bounds_15_12864 : exactInterval 15 12864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12864 : oddCount 12864 15 = 4 ∧ acceleratedOrbit 15 12864 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12864) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12864.1, data_15_12864.2]

/-- Complete interval computation for depth 15, residue 12865. -/
theorem bounds_15_12865 : exactInterval 15 12865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12865 : oddCount 12865 15 = 6 ∧ acceleratedOrbit 15 12865 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12865) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12865.1, data_15_12865.2]

/-- Complete interval computation for depth 15, residue 12866. -/
theorem bounds_15_12866 : exactInterval 15 12866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12866 : oddCount 12866 15 = 6 ∧ acceleratedOrbit 15 12866 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12866) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12866.1, data_15_12866.2]

/-- Complete interval computation for depth 15, residue 12867. -/
theorem bounds_15_12867 : exactInterval 15 12867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12867 : oddCount 12867 15 = 6 ∧ acceleratedOrbit 15 12867 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12867) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12867.1, data_15_12867.2]

/-- Complete interval computation for depth 15, residue 12868. -/
theorem bounds_15_12868 : exactInterval 15 12868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12868 : oddCount 12868 15 = 8 ∧ acceleratedOrbit 15 12868 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12868) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12868.1, data_15_12868.2]

/-- Complete interval computation for depth 15, residue 12869. -/
theorem bounds_15_12869 : exactInterval 15 12869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12869 : oddCount 12869 15 = 8 ∧ acceleratedOrbit 15 12869 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12869) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12869.1, data_15_12869.2]

/-- Complete interval computation for depth 15, residue 12870. -/
theorem bounds_15_12870 : exactInterval 15 12870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12870 : oddCount 12870 15 = 8 ∧ acceleratedOrbit 15 12870 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12870) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12870.1, data_15_12870.2]

/-- Complete interval computation for depth 15, residue 12871. -/
theorem bounds_15_12871 : exactInterval 15 12871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12871 : oddCount 12871 15 = 8 ∧ acceleratedOrbit 15 12871 = 2578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12871) = 3 ^ 8 * m + 2578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12871.1, data_15_12871.2]

/-- Complete interval computation for depth 15, residue 12872. -/
theorem bounds_15_12872 : exactInterval 15 12872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12872 : oddCount 12872 15 = 8 ∧ acceleratedOrbit 15 12872 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12872) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12872.1, data_15_12872.2]

/-- Complete interval computation for depth 15, residue 12873. -/
theorem bounds_15_12873 : exactInterval 15 12873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12873 : oddCount 12873 15 = 9 ∧ acceleratedOrbit 15 12873 = 7735 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12873) = 3 ^ 9 * m + 7735 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12873.1, data_15_12873.2]

/-- Complete interval computation for depth 15, residue 12874. -/
theorem bounds_15_12874 : exactInterval 15 12874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12874 : oddCount 12874 15 = 8 ∧ acceleratedOrbit 15 12874 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12874) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12874.1, data_15_12874.2]

/-- Complete interval computation for depth 15, residue 12875. -/
theorem bounds_15_12875 : exactInterval 15 12875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12875 : oddCount 12875 15 = 8 ∧ acceleratedOrbit 15 12875 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12875) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12875.1, data_15_12875.2]

/-- Complete interval computation for depth 15, residue 12876. -/
theorem bounds_15_12876 : exactInterval 15 12876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12876 : oddCount 12876 15 = 8 ∧ acceleratedOrbit 15 12876 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12876) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12876.1, data_15_12876.2]

end Collatz.Research.PassageAtlas.Batch0393
