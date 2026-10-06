import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0882

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28868. -/
theorem bounds_15_28868 : exactInterval 15 28868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28868 : oddCount 28868 15 = 6 ∧ acceleratedOrbit 15 28868 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28868) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28868.1, data_15_28868.2]

/-- Complete interval computation for depth 15, residue 28869. -/
theorem bounds_15_28869 : exactInterval 15 28869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28869 : oddCount 28869 15 = 6 ∧ acceleratedOrbit 15 28869 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28869) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28869.1, data_15_28869.2]

/-- Complete interval computation for depth 15, residue 28870. -/
theorem bounds_15_28870 : exactInterval 15 28870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28870 : oddCount 28870 15 = 6 ∧ acceleratedOrbit 15 28870 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28870) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28870.1, data_15_28870.2]

/-- Complete interval computation for depth 15, residue 28871. -/
theorem bounds_15_28871 : exactInterval 15 28871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28871 : oddCount 28871 15 = 9 ∧ acceleratedOrbit 15 28871 = 17344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28871) = 3 ^ 9 * m + 17344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28871.1, data_15_28871.2]

/-- Complete interval computation for depth 15, residue 28872. -/
theorem bounds_15_28872 : exactInterval 15 28872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28872 : oddCount 28872 15 = 6 ∧ acceleratedOrbit 15 28872 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28872) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28872.1, data_15_28872.2]

/-- Complete interval computation for depth 15, residue 28873. -/
theorem bounds_15_28873 : exactInterval 15 28873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28873 : oddCount 28873 15 = 6 ∧ acceleratedOrbit 15 28873 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28873) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28873.1, data_15_28873.2]

/-- Complete interval computation for depth 15, residue 28874. -/
theorem bounds_15_28874 : exactInterval 15 28874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28874 : oddCount 28874 15 = 6 ∧ acceleratedOrbit 15 28874 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28874) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28874.1, data_15_28874.2]

/-- Complete interval computation for depth 15, residue 28875. -/
theorem bounds_15_28875 : exactInterval 15 28875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28875 : oddCount 28875 15 = 7 ∧ acceleratedOrbit 15 28875 = 1928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28875) = 3 ^ 7 * m + 1928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28875.1, data_15_28875.2]

/-- Complete interval computation for depth 15, residue 28876. -/
theorem bounds_15_28876 : exactInterval 15 28876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28876 : oddCount 28876 15 = 6 ∧ acceleratedOrbit 15 28876 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28876) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28876.1, data_15_28876.2]

/-- Complete interval computation for depth 15, residue 28877. -/
theorem bounds_15_28877 : exactInterval 15 28877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28877 : oddCount 28877 15 = 6 ∧ acceleratedOrbit 15 28877 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28877) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28877.1, data_15_28877.2]

/-- Complete interval computation for depth 15, residue 28878. -/
theorem bounds_15_28878 : exactInterval 15 28878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28878 : oddCount 28878 15 = 9 ∧ acceleratedOrbit 15 28878 = 17348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28878) = 3 ^ 9 * m + 17348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28878.1, data_15_28878.2]

/-- Complete interval computation for depth 15, residue 28879. -/
theorem bounds_15_28879 : exactInterval 15 28879 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28879) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28879 : oddCount 28879 15 = 9 ∧ acceleratedOrbit 15 28879 = 17348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28879) = 3 ^ 9 * m + 17348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28879.1, data_15_28879.2]

/-- Complete interval computation for depth 15, residue 28880. -/
theorem bounds_15_28880 : exactInterval 15 28880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28880 : oddCount 28880 15 = 6 ∧ acceleratedOrbit 15 28880 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28880) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28880.1, data_15_28880.2]

/-- Complete interval computation for depth 15, residue 28881. -/
theorem bounds_15_28881 : exactInterval 15 28881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28881 : oddCount 28881 15 = 7 ∧ acceleratedOrbit 15 28881 = 1928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28881) = 3 ^ 7 * m + 1928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28881.1, data_15_28881.2]

/-- Complete interval computation for depth 15, residue 28882. -/
theorem bounds_15_28882 : exactInterval 15 28882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28882 : oddCount 28882 15 = 7 ∧ acceleratedOrbit 15 28882 = 1928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28882) = 3 ^ 7 * m + 1928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28882.1, data_15_28882.2]

/-- Complete interval computation for depth 15, residue 28883. -/
theorem bounds_15_28883 : exactInterval 15 28883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28883 : oddCount 28883 15 = 7 ∧ acceleratedOrbit 15 28883 = 1928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28883) = 3 ^ 7 * m + 1928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28883.1, data_15_28883.2]

/-- Complete interval computation for depth 15, residue 28884. -/
theorem bounds_15_28884 : exactInterval 15 28884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28884 : oddCount 28884 15 = 6 ∧ acceleratedOrbit 15 28884 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28884) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28884.1, data_15_28884.2]

/-- Complete interval computation for depth 15, residue 28885. -/
theorem bounds_15_28885 : exactInterval 15 28885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28885 : oddCount 28885 15 = 6 ∧ acceleratedOrbit 15 28885 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28885) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28885.1, data_15_28885.2]

/-- Complete interval computation for depth 15, residue 28886. -/
theorem bounds_15_28886 : exactInterval 15 28886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28886 : oddCount 28886 15 = 9 ∧ acceleratedOrbit 15 28886 = 17354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28886) = 3 ^ 9 * m + 17354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28886.1, data_15_28886.2]

/-- Complete interval computation for depth 15, residue 28887. -/
theorem bounds_15_28887 : exactInterval 15 28887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28887 : oddCount 28887 15 = 9 ∧ acceleratedOrbit 15 28887 = 17354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28887) = 3 ^ 9 * m + 17354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28887.1, data_15_28887.2]

/-- Complete interval computation for depth 15, residue 28888. -/
theorem bounds_15_28888 : exactInterval 15 28888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28888 : oddCount 28888 15 = 9 ∧ acceleratedOrbit 15 28888 = 17360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28888) = 3 ^ 9 * m + 17360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28888.1, data_15_28888.2]

/-- Complete interval computation for depth 15, residue 28889. -/
theorem bounds_15_28889 : exactInterval 15 28889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28889 : oddCount 28889 15 = 9 ∧ acceleratedOrbit 15 28889 = 17360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28889) = 3 ^ 9 * m + 17360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28889.1, data_15_28889.2]

/-- Complete interval computation for depth 15, residue 28890. -/
theorem bounds_15_28890 : exactInterval 15 28890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28890 : oddCount 28890 15 = 9 ∧ acceleratedOrbit 15 28890 = 17360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28890) = 3 ^ 9 * m + 17360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28890.1, data_15_28890.2]

/-- Complete interval computation for depth 15, residue 28891. -/
theorem bounds_15_28891 : exactInterval 15 28891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28891 : oddCount 28891 15 = 9 ∧ acceleratedOrbit 15 28891 = 17356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28891) = 3 ^ 9 * m + 17356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28891.1, data_15_28891.2]

/-- Complete interval computation for depth 15, residue 28892. -/
theorem bounds_15_28892 : exactInterval 15 28892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28892 : oddCount 28892 15 = 9 ∧ acceleratedOrbit 15 28892 = 17360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28892) = 3 ^ 9 * m + 17360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28892.1, data_15_28892.2]

/-- Complete interval computation for depth 15, residue 28893. -/
theorem bounds_15_28893 : exactInterval 15 28893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28893 : oddCount 28893 15 = 9 ∧ acceleratedOrbit 15 28893 = 17360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28893) = 3 ^ 9 * m + 17360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28893.1, data_15_28893.2]

/-- Complete interval computation for depth 15, residue 28894. -/
theorem bounds_15_28894 : exactInterval 15 28894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28894 : oddCount 28894 15 = 10 ∧ acceleratedOrbit 15 28894 = 52073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28894) = 3 ^ 10 * m + 52073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28894.1, data_15_28894.2]

/-- Complete interval computation for depth 15, residue 28895. -/
theorem bounds_15_28895 : exactInterval 15 28895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28895 : oddCount 28895 15 = 10 ∧ acceleratedOrbit 15 28895 = 52073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28895) = 3 ^ 10 * m + 52073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28895.1, data_15_28895.2]

/-- Complete interval computation for depth 15, residue 28896. -/
theorem bounds_15_28896 : exactInterval 15 28896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28896 : oddCount 28896 15 = 5 ∧ acceleratedOrbit 15 28896 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28896) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28896.1, data_15_28896.2]

/-- Complete interval computation for depth 15, residue 28897. -/
theorem bounds_15_28897 : exactInterval 15 28897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28897 : oddCount 28897 15 = 10 ∧ acceleratedOrbit 15 28897 = 52078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28897) = 3 ^ 10 * m + 52078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28897.1, data_15_28897.2]

/-- Complete interval computation for depth 15, residue 28898. -/
theorem bounds_15_28898 : exactInterval 15 28898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28898 : oddCount 28898 15 = 6 ∧ acceleratedOrbit 15 28898 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28898) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28898.1, data_15_28898.2]

/-- Complete interval computation for depth 15, residue 28899. -/
theorem bounds_15_28899 : exactInterval 15 28899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28899 : oddCount 28899 15 = 6 ∧ acceleratedOrbit 15 28899 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28899) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28899.1, data_15_28899.2]

/-- Complete interval computation for depth 15, residue 28900. -/
theorem bounds_15_28900 : exactInterval 15 28900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28900 : oddCount 28900 15 = 7 ∧ acceleratedOrbit 15 28900 = 1930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28900) = 3 ^ 7 * m + 1930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28900.1, data_15_28900.2]

end Collatz.Research.PassageAtlas.Batch0882
