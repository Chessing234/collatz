import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0943

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30867. -/
theorem bounds_15_30867 : exactInterval 15 30867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30867 : oddCount 30867 15 = 9 ∧ acceleratedOrbit 15 30867 = 18544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30867) = 3 ^ 9 * m + 18544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30867.1, data_15_30867.2]

/-- Complete interval computation for depth 15, residue 30868. -/
theorem bounds_15_30868 : exactInterval 15 30868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30868 : oddCount 30868 15 = 7 ∧ acceleratedOrbit 15 30868 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30868) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30868.1, data_15_30868.2]

/-- Complete interval computation for depth 15, residue 30869. -/
theorem bounds_15_30869 : exactInterval 15 30869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30869 : oddCount 30869 15 = 7 ∧ acceleratedOrbit 15 30869 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30869) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30869.1, data_15_30869.2]

/-- Complete interval computation for depth 15, residue 30870. -/
theorem bounds_15_30870 : exactInterval 15 30870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30870 : oddCount 30870 15 = 6 ∧ acceleratedOrbit 15 30870 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30870) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30870.1, data_15_30870.2]

/-- Complete interval computation for depth 15, residue 30871. -/
theorem bounds_15_30871 : exactInterval 15 30871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30871 : oddCount 30871 15 = 6 ∧ acceleratedOrbit 15 30871 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30871) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30871.1, data_15_30871.2]

/-- Complete interval computation for depth 15, residue 30872. -/
theorem bounds_15_30872 : exactInterval 15 30872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30872 : oddCount 30872 15 = 7 ∧ acceleratedOrbit 15 30872 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30872) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30872.1, data_15_30872.2]

/-- Complete interval computation for depth 15, residue 30873. -/
theorem bounds_15_30873 : exactInterval 15 30873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30873 : oddCount 30873 15 = 10 ∧ acceleratedOrbit 15 30873 = 55646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30873) = 3 ^ 10 * m + 55646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30873.1, data_15_30873.2]

/-- Complete interval computation for depth 15, residue 30874. -/
theorem bounds_15_30874 : exactInterval 15 30874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30874 : oddCount 30874 15 = 7 ∧ acceleratedOrbit 15 30874 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30874) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30874.1, data_15_30874.2]

/-- Complete interval computation for depth 15, residue 30875. -/
theorem bounds_15_30875 : exactInterval 15 30875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30875 : oddCount 30875 15 = 9 ∧ acceleratedOrbit 15 30875 = 18548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30875) = 3 ^ 9 * m + 18548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30875.1, data_15_30875.2]

/-- Complete interval computation for depth 15, residue 30876. -/
theorem bounds_15_30876 : exactInterval 15 30876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30876 : oddCount 30876 15 = 5 ∧ acceleratedOrbit 15 30876 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30876) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30876.1, data_15_30876.2]

/-- Complete interval computation for depth 15, residue 30877. -/
theorem bounds_15_30877 : exactInterval 15 30877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30877 : oddCount 30877 15 = 5 ∧ acceleratedOrbit 15 30877 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30877) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30877.1, data_15_30877.2]

/-- Complete interval computation for depth 15, residue 30878. -/
theorem bounds_15_30878 : exactInterval 15 30878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30878 : oddCount 30878 15 = 5 ∧ acceleratedOrbit 15 30878 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30878) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30878.1, data_15_30878.2]

/-- Complete interval computation for depth 15, residue 30879. -/
theorem bounds_15_30879 : exactInterval 15 30879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30879 : oddCount 30879 15 = 14 ∧ acceleratedOrbit 15 30879 = 4507406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30879) = 3 ^ 14 * m + 4507406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30879.1, data_15_30879.2]

/-- Complete interval computation for depth 15, residue 30880. -/
theorem bounds_15_30880 : exactInterval 15 30880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30880 : oddCount 30880 15 = 3 ∧ acceleratedOrbit 15 30880 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30880) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30880.1, data_15_30880.2]

/-- Complete interval computation for depth 15, residue 30881. -/
theorem bounds_15_30881 : exactInterval 15 30881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30881 : oddCount 30881 15 = 8 ∧ acceleratedOrbit 15 30881 = 6184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30881) = 3 ^ 8 * m + 6184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30881.1, data_15_30881.2]

/-- Complete interval computation for depth 15, residue 30882. -/
theorem bounds_15_30882 : exactInterval 15 30882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30882 : oddCount 30882 15 = 7 ∧ acceleratedOrbit 15 30882 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30882) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30882.1, data_15_30882.2]

/-- Complete interval computation for depth 15, residue 30883. -/
theorem bounds_15_30883 : exactInterval 15 30883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30883 : oddCount 30883 15 = 7 ∧ acceleratedOrbit 15 30883 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30883) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30883.1, data_15_30883.2]

/-- Complete interval computation for depth 15, residue 30884. -/
theorem bounds_15_30884 : exactInterval 15 30884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30884 : oddCount 30884 15 = 10 ∧ acceleratedOrbit 15 30884 = 55667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30884) = 3 ^ 10 * m + 55667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30884.1, data_15_30884.2]

/-- Complete interval computation for depth 15, residue 30885. -/
theorem bounds_15_30885 : exactInterval 15 30885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30885 : oddCount 30885 15 = 10 ∧ acceleratedOrbit 15 30885 = 55667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30885) = 3 ^ 10 * m + 55667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30885.1, data_15_30885.2]

/-- Complete interval computation for depth 15, residue 30886. -/
theorem bounds_15_30886 : exactInterval 15 30886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30886 : oddCount 30886 15 = 10 ∧ acceleratedOrbit 15 30886 = 55667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30886) = 3 ^ 10 * m + 55667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30886.1, data_15_30886.2]

/-- Complete interval computation for depth 15, residue 30887. -/
theorem bounds_15_30887 : exactInterval 15 30887 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30887) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30887 : oddCount 30887 15 = 9 ∧ acceleratedOrbit 15 30887 = 18554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30887) = 3 ^ 9 * m + 18554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30887.1, data_15_30887.2]

/-- Complete interval computation for depth 15, residue 30888. -/
theorem bounds_15_30888 : exactInterval 15 30888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30888 : oddCount 30888 15 = 3 ∧ acceleratedOrbit 15 30888 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30888) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30888.1, data_15_30888.2]

/-- Complete interval computation for depth 15, residue 30889. -/
theorem bounds_15_30889 : exactInterval 15 30889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30889 : oddCount 30889 15 = 10 ∧ acceleratedOrbit 15 30889 = 55666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30889) = 3 ^ 10 * m + 55666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30889.1, data_15_30889.2]

/-- Complete interval computation for depth 15, residue 30890. -/
theorem bounds_15_30890 : exactInterval 15 30890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30890 : oddCount 30890 15 = 3 ∧ acceleratedOrbit 15 30890 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30890) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30890.1, data_15_30890.2]

/-- Complete interval computation for depth 15, residue 30891. -/
theorem bounds_15_30891 : exactInterval 15 30891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30891 : oddCount 30891 15 = 7 ∧ acceleratedOrbit 15 30891 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30891) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30891.1, data_15_30891.2]

/-- Complete interval computation for depth 15, residue 30892. -/
theorem bounds_15_30892 : exactInterval 15 30892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30892 : oddCount 30892 15 = 6 ∧ acceleratedOrbit 15 30892 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30892) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30892.1, data_15_30892.2]

/-- Complete interval computation for depth 15, residue 30893. -/
theorem bounds_15_30893 : exactInterval 15 30893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30893 : oddCount 30893 15 = 6 ∧ acceleratedOrbit 15 30893 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30893) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30893.1, data_15_30893.2]

/-- Complete interval computation for depth 15, residue 30894. -/
theorem bounds_15_30894 : exactInterval 15 30894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30894 : oddCount 30894 15 = 6 ∧ acceleratedOrbit 15 30894 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30894) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30894.1, data_15_30894.2]

/-- Complete interval computation for depth 15, residue 30895. -/
theorem bounds_15_30895 : exactInterval 15 30895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30895 : oddCount 30895 15 = 9 ∧ acceleratedOrbit 15 30895 = 18559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30895) = 3 ^ 9 * m + 18559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30895.1, data_15_30895.2]

/-- Complete interval computation for depth 15, residue 30896. -/
theorem bounds_15_30896 : exactInterval 15 30896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30896 : oddCount 30896 15 = 7 ∧ acceleratedOrbit 15 30896 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30896) = 3 ^ 7 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30896.1, data_15_30896.2]

/-- Complete interval computation for depth 15, residue 30897. -/
theorem bounds_15_30897 : exactInterval 15 30897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30897 : oddCount 30897 15 = 7 ∧ acceleratedOrbit 15 30897 = 2063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30897) = 3 ^ 7 * m + 2063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30897.1, data_15_30897.2]

/-- Complete interval computation for depth 15, residue 30898. -/
theorem bounds_15_30898 : exactInterval 15 30898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30898 : oddCount 30898 15 = 7 ∧ acceleratedOrbit 15 30898 = 2063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30898) = 3 ^ 7 * m + 2063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30898.1, data_15_30898.2]

/-- Complete interval computation for depth 15, residue 30899. -/
theorem bounds_15_30899 : exactInterval 15 30899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30899 : oddCount 30899 15 = 7 ∧ acceleratedOrbit 15 30899 = 2063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30899) = 3 ^ 7 * m + 2063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30899.1, data_15_30899.2]

end Collatz.Research.PassageAtlas.Batch0943
