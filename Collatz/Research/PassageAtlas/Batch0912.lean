import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0912

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29851. -/
theorem bounds_15_29851 : exactInterval 15 29851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29851 : oddCount 29851 15 = 9 ∧ acceleratedOrbit 15 29851 = 17932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29851) = 3 ^ 9 * m + 17932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29851.1, data_15_29851.2]

/-- Complete interval computation for depth 15, residue 29852. -/
theorem bounds_15_29852 : exactInterval 15 29852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29852 : oddCount 29852 15 = 7 ∧ acceleratedOrbit 15 29852 = 1993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29852) = 3 ^ 7 * m + 1993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29852.1, data_15_29852.2]

/-- Complete interval computation for depth 15, residue 29853. -/
theorem bounds_15_29853 : exactInterval 15 29853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29853 : oddCount 29853 15 = 7 ∧ acceleratedOrbit 15 29853 = 1993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29853) = 3 ^ 7 * m + 1993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29853.1, data_15_29853.2]

/-- Complete interval computation for depth 15, residue 29854. -/
theorem bounds_15_29854 : exactInterval 15 29854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29854 : oddCount 29854 15 = 7 ∧ acceleratedOrbit 15 29854 = 1993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29854) = 3 ^ 7 * m + 1993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29854.1, data_15_29854.2]

/-- Complete interval computation for depth 15, residue 29855. -/
theorem bounds_15_29855 : exactInterval 15 29855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29855 : oddCount 29855 15 = 12 ∧ acceleratedOrbit 15 29855 = 484217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29855) = 3 ^ 12 * m + 484217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29855.1, data_15_29855.2]

/-- Complete interval computation for depth 15, residue 29856. -/
theorem bounds_15_29856 : exactInterval 15 29856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29856 : oddCount 29856 15 = 6 ∧ acceleratedOrbit 15 29856 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29856) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29856.1, data_15_29856.2]

/-- Complete interval computation for depth 15, residue 29857. -/
theorem bounds_15_29857 : exactInterval 15 29857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29857 : oddCount 29857 15 = 10 ∧ acceleratedOrbit 15 29857 = 53810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29857) = 3 ^ 10 * m + 53810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29857.1, data_15_29857.2]

/-- Complete interval computation for depth 15, residue 29858. -/
theorem bounds_15_29858 : exactInterval 15 29858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29858 : oddCount 29858 15 = 9 ∧ acceleratedOrbit 15 29858 = 17941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29858) = 3 ^ 9 * m + 17941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29858.1, data_15_29858.2]

/-- Complete interval computation for depth 15, residue 29859. -/
theorem bounds_15_29859 : exactInterval 15 29859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29859 : oddCount 29859 15 = 9 ∧ acceleratedOrbit 15 29859 = 17941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29859) = 3 ^ 9 * m + 17941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29859.1, data_15_29859.2]

/-- Complete interval computation for depth 15, residue 29860. -/
theorem bounds_15_29860 : exactInterval 15 29860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29860 : oddCount 29860 15 = 9 ∧ acceleratedOrbit 15 29860 = 17941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29860) = 3 ^ 9 * m + 17941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29860.1, data_15_29860.2]

/-- Complete interval computation for depth 15, residue 29861. -/
theorem bounds_15_29861 : exactInterval 15 29861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29861 : oddCount 29861 15 = 9 ∧ acceleratedOrbit 15 29861 = 17941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29861) = 3 ^ 9 * m + 17941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29861.1, data_15_29861.2]

/-- Complete interval computation for depth 15, residue 29862. -/
theorem bounds_15_29862 : exactInterval 15 29862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29862 : oddCount 29862 15 = 9 ∧ acceleratedOrbit 15 29862 = 17941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29862) = 3 ^ 9 * m + 17941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29862.1, data_15_29862.2]

/-- Complete interval computation for depth 15, residue 29863. -/
theorem bounds_15_29863 : exactInterval 15 29863 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29863) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29863 : oddCount 29863 15 = 9 ∧ acceleratedOrbit 15 29863 = 17939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29863) = 3 ^ 9 * m + 17939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29863.1, data_15_29863.2]

/-- Complete interval computation for depth 15, residue 29864. -/
theorem bounds_15_29864 : exactInterval 15 29864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29864 : oddCount 29864 15 = 6 ∧ acceleratedOrbit 15 29864 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29864) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29864.1, data_15_29864.2]

/-- Complete interval computation for depth 15, residue 29865. -/
theorem bounds_15_29865 : exactInterval 15 29865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29865 : oddCount 29865 15 = 10 ∧ acceleratedOrbit 15 29865 = 53821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29865) = 3 ^ 10 * m + 53821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29865.1, data_15_29865.2]

/-- Complete interval computation for depth 15, residue 29866. -/
theorem bounds_15_29866 : exactInterval 15 29866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29866 : oddCount 29866 15 = 6 ∧ acceleratedOrbit 15 29866 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29866) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29866.1, data_15_29866.2]

/-- Complete interval computation for depth 15, residue 29867. -/
theorem bounds_15_29867 : exactInterval 15 29867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29867 : oddCount 29867 15 = 6 ∧ acceleratedOrbit 15 29867 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29867) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29867.1, data_15_29867.2]

/-- Complete interval computation for depth 15, residue 29868. -/
theorem bounds_15_29868 : exactInterval 15 29868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29868 : oddCount 29868 15 = 8 ∧ acceleratedOrbit 15 29868 = 5984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29868) = 3 ^ 8 * m + 5984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29868.1, data_15_29868.2]

/-- Complete interval computation for depth 15, residue 29869. -/
theorem bounds_15_29869 : exactInterval 15 29869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29869 : oddCount 29869 15 = 8 ∧ acceleratedOrbit 15 29869 = 5984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29869) = 3 ^ 8 * m + 5984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29869.1, data_15_29869.2]

/-- Complete interval computation for depth 15, residue 29870. -/
theorem bounds_15_29870 : exactInterval 15 29870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29870 : oddCount 29870 15 = 8 ∧ acceleratedOrbit 15 29870 = 5984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29870) = 3 ^ 8 * m + 5984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29870.1, data_15_29870.2]

/-- Complete interval computation for depth 15, residue 29871. -/
theorem bounds_15_29871 : exactInterval 15 29871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29871 : oddCount 29871 15 = 9 ∧ acceleratedOrbit 15 29871 = 17945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29871) = 3 ^ 9 * m + 17945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29871.1, data_15_29871.2]

/-- Complete interval computation for depth 15, residue 29872. -/
theorem bounds_15_29872 : exactInterval 15 29872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29872 : oddCount 29872 15 = 4 ∧ acceleratedOrbit 15 29872 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29872) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29872.1, data_15_29872.2]

/-- Complete interval computation for depth 15, residue 29873. -/
theorem bounds_15_29873 : exactInterval 15 29873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29873 : oddCount 29873 15 = 8 ∧ acceleratedOrbit 15 29873 = 5984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29873) = 3 ^ 8 * m + 5984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29873.1, data_15_29873.2]

/-- Complete interval computation for depth 15, residue 29874. -/
theorem bounds_15_29874 : exactInterval 15 29874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29874 : oddCount 29874 15 = 8 ∧ acceleratedOrbit 15 29874 = 5984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29874) = 3 ^ 8 * m + 5984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29874.1, data_15_29874.2]

/-- Complete interval computation for depth 15, residue 29875. -/
theorem bounds_15_29875 : exactInterval 15 29875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29875 : oddCount 29875 15 = 8 ∧ acceleratedOrbit 15 29875 = 5984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29875) = 3 ^ 8 * m + 5984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29875.1, data_15_29875.2]

/-- Complete interval computation for depth 15, residue 29876. -/
theorem bounds_15_29876 : exactInterval 15 29876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29876 : oddCount 29876 15 = 4 ∧ acceleratedOrbit 15 29876 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29876) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29876.1, data_15_29876.2]

/-- Complete interval computation for depth 15, residue 29877. -/
theorem bounds_15_29877 : exactInterval 15 29877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29877 : oddCount 29877 15 = 4 ∧ acceleratedOrbit 15 29877 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29877) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29877.1, data_15_29877.2]

/-- Complete interval computation for depth 15, residue 29878. -/
theorem bounds_15_29878 : exactInterval 15 29878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29878 : oddCount 29878 15 = 8 ∧ acceleratedOrbit 15 29878 = 5983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29878) = 3 ^ 8 * m + 5983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29878.1, data_15_29878.2]

/-- Complete interval computation for depth 15, residue 29879. -/
theorem bounds_15_29879 : exactInterval 15 29879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29879 : oddCount 29879 15 = 8 ∧ acceleratedOrbit 15 29879 = 5983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29879) = 3 ^ 8 * m + 5983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29879.1, data_15_29879.2]

/-- Complete interval computation for depth 15, residue 29880. -/
theorem bounds_15_29880 : exactInterval 15 29880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29880 : oddCount 29880 15 = 4 ∧ acceleratedOrbit 15 29880 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29880) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29880.1, data_15_29880.2]

/-- Complete interval computation for depth 15, residue 29881. -/
theorem bounds_15_29881 : exactInterval 15 29881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29881 : oddCount 29881 15 = 10 ∧ acceleratedOrbit 15 29881 = 53855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29881) = 3 ^ 10 * m + 53855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29881.1, data_15_29881.2]

/-- Complete interval computation for depth 15, residue 29882. -/
theorem bounds_15_29882 : exactInterval 15 29882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29882 : oddCount 29882 15 = 4 ∧ acceleratedOrbit 15 29882 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29882) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29882.1, data_15_29882.2]

/-- Complete interval computation for depth 15, residue 29883. -/
theorem bounds_15_29883 : exactInterval 15 29883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29883 : oddCount 29883 15 = 10 ∧ acceleratedOrbit 15 29883 = 53855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29883) = 3 ^ 10 * m + 53855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29883.1, data_15_29883.2]

end Collatz.Research.PassageAtlas.Batch0912
