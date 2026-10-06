import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0760

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24870. -/
theorem bounds_15_24870 : exactInterval 15 24870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24870 : oddCount 24870 15 = 9 ∧ acceleratedOrbit 15 24870 = 14944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24870) = 3 ^ 9 * m + 14944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24870.1, data_15_24870.2]

/-- Complete interval computation for depth 15, residue 24871. -/
theorem bounds_15_24871 : exactInterval 15 24871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24871 : oddCount 24871 15 = 9 ∧ acceleratedOrbit 15 24871 = 14941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24871) = 3 ^ 9 * m + 14941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24871.1, data_15_24871.2]

/-- Complete interval computation for depth 15, residue 24872. -/
theorem bounds_15_24872 : exactInterval 15 24872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24872 : oddCount 24872 15 = 7 ∧ acceleratedOrbit 15 24872 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24872) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24872.1, data_15_24872.2]

/-- Complete interval computation for depth 15, residue 24873. -/
theorem bounds_15_24873 : exactInterval 15 24873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24873 : oddCount 24873 15 = 9 ∧ acceleratedOrbit 15 24873 = 14942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24873) = 3 ^ 9 * m + 14942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24873.1, data_15_24873.2]

/-- Complete interval computation for depth 15, residue 24874. -/
theorem bounds_15_24874 : exactInterval 15 24874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24874 : oddCount 24874 15 = 7 ∧ acceleratedOrbit 15 24874 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24874) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24874.1, data_15_24874.2]

/-- Complete interval computation for depth 15, residue 24875. -/
theorem bounds_15_24875 : exactInterval 15 24875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24875 : oddCount 24875 15 = 10 ∧ acceleratedOrbit 15 24875 = 44833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24875) = 3 ^ 10 * m + 44833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24875.1, data_15_24875.2]

/-- Complete interval computation for depth 15, residue 24876. -/
theorem bounds_15_24876 : exactInterval 15 24876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24876 : oddCount 24876 15 = 4 ∧ acceleratedOrbit 15 24876 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24876) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24876.1, data_15_24876.2]

/-- Complete interval computation for depth 15, residue 24877. -/
theorem bounds_15_24877 : exactInterval 15 24877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24877 : oddCount 24877 15 = 4 ∧ acceleratedOrbit 15 24877 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24877) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24877.1, data_15_24877.2]

/-- Complete interval computation for depth 15, residue 24878. -/
theorem bounds_15_24878 : exactInterval 15 24878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24878 : oddCount 24878 15 = 4 ∧ acceleratedOrbit 15 24878 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24878) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24878.1, data_15_24878.2]

/-- Complete interval computation for depth 15, residue 24879. -/
theorem bounds_15_24879 : exactInterval 15 24879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24879 : oddCount 24879 15 = 10 ∧ acceleratedOrbit 15 24879 = 44837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24879) = 3 ^ 10 * m + 44837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24879.1, data_15_24879.2]

/-- Complete interval computation for depth 15, residue 24880. -/
theorem bounds_15_24880 : exactInterval 15 24880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24880 : oddCount 24880 15 = 7 ∧ acceleratedOrbit 15 24880 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24880) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24880.1, data_15_24880.2]

/-- Complete interval computation for depth 15, residue 24881. -/
theorem bounds_15_24881 : exactInterval 15 24881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24881 : oddCount 24881 15 = 8 ∧ acceleratedOrbit 15 24881 = 4985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24881) = 3 ^ 8 * m + 4985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24881.1, data_15_24881.2]

/-- Complete interval computation for depth 15, residue 24882. -/
theorem bounds_15_24882 : exactInterval 15 24882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24882 : oddCount 24882 15 = 8 ∧ acceleratedOrbit 15 24882 = 4985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24882) = 3 ^ 8 * m + 4985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24882.1, data_15_24882.2]

/-- Complete interval computation for depth 15, residue 24883. -/
theorem bounds_15_24883 : exactInterval 15 24883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24883 : oddCount 24883 15 = 8 ∧ acceleratedOrbit 15 24883 = 4985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24883) = 3 ^ 8 * m + 4985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24883.1, data_15_24883.2]

/-- Complete interval computation for depth 15, residue 24884. -/
theorem bounds_15_24884 : exactInterval 15 24884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24884 : oddCount 24884 15 = 7 ∧ acceleratedOrbit 15 24884 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24884) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24884.1, data_15_24884.2]

/-- Complete interval computation for depth 15, residue 24885. -/
theorem bounds_15_24885 : exactInterval 15 24885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24885 : oddCount 24885 15 = 7 ∧ acceleratedOrbit 15 24885 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24885) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24885.1, data_15_24885.2]

/-- Complete interval computation for depth 15, residue 24886. -/
theorem bounds_15_24886 : exactInterval 15 24886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24886 : oddCount 24886 15 = 9 ∧ acceleratedOrbit 15 24886 = 14951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24886) = 3 ^ 9 * m + 14951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24886.1, data_15_24886.2]

/-- Complete interval computation for depth 15, residue 24887. -/
theorem bounds_15_24887 : exactInterval 15 24887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24887 : oddCount 24887 15 = 9 ∧ acceleratedOrbit 15 24887 = 14951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24887) = 3 ^ 9 * m + 14951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24887.1, data_15_24887.2]

/-- Complete interval computation for depth 15, residue 24888. -/
theorem bounds_15_24888 : exactInterval 15 24888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24888 : oddCount 24888 15 = 6 ∧ acceleratedOrbit 15 24888 = 554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24888) = 3 ^ 6 * m + 554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24888.1, data_15_24888.2]

/-- Complete interval computation for depth 15, residue 24889. -/
theorem bounds_15_24889 : exactInterval 15 24889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24889 : oddCount 24889 15 = 8 ∧ acceleratedOrbit 15 24889 = 4984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24889) = 3 ^ 8 * m + 4984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24889.1, data_15_24889.2]

/-- Complete interval computation for depth 15, residue 24890. -/
theorem bounds_15_24890 : exactInterval 15 24890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24890 : oddCount 24890 15 = 6 ∧ acceleratedOrbit 15 24890 = 554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24890) = 3 ^ 6 * m + 554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24890.1, data_15_24890.2]

/-- Complete interval computation for depth 15, residue 24891. -/
theorem bounds_15_24891 : exactInterval 15 24891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24891 : oddCount 24891 15 = 6 ∧ acceleratedOrbit 15 24891 = 554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24891) = 3 ^ 6 * m + 554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24891.1, data_15_24891.2]

/-- Complete interval computation for depth 15, residue 24892. -/
theorem bounds_15_24892 : exactInterval 15 24892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24892 : oddCount 24892 15 = 6 ∧ acceleratedOrbit 15 24892 = 554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24892) = 3 ^ 6 * m + 554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24892.1, data_15_24892.2]

/-- Complete interval computation for depth 15, residue 24893. -/
theorem bounds_15_24893 : exactInterval 15 24893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24893 : oddCount 24893 15 = 6 ∧ acceleratedOrbit 15 24893 = 554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24893) = 3 ^ 6 * m + 554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24893.1, data_15_24893.2]

/-- Complete interval computation for depth 15, residue 24894. -/
theorem bounds_15_24894 : exactInterval 15 24894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24894 : oddCount 24894 15 = 12 ∧ acceleratedOrbit 15 24894 = 403775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24894) = 3 ^ 12 * m + 403775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24894.1, data_15_24894.2]

/-- Complete interval computation for depth 15, residue 24895. -/
theorem bounds_15_24895 : exactInterval 15 24895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24895 : oddCount 24895 15 = 12 ∧ acceleratedOrbit 15 24895 = 403775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24895) = 3 ^ 12 * m + 403775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24895.1, data_15_24895.2]

/-- Complete interval computation for depth 15, residue 24896. -/
theorem bounds_15_24896 : exactInterval 15 24896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24896 : oddCount 24896 15 = 5 ∧ acceleratedOrbit 15 24896 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24896) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24896.1, data_15_24896.2]

/-- Complete interval computation for depth 15, residue 24897. -/
theorem bounds_15_24897 : exactInterval 15 24897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24897 : oddCount 24897 15 = 7 ∧ acceleratedOrbit 15 24897 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24897) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24897.1, data_15_24897.2]

/-- Complete interval computation for depth 15, residue 24898. -/
theorem bounds_15_24898 : exactInterval 15 24898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24898 : oddCount 24898 15 = 9 ∧ acceleratedOrbit 15 24898 = 14960 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24898) = 3 ^ 9 * m + 14960 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24898.1, data_15_24898.2]

/-- Complete interval computation for depth 15, residue 24899. -/
theorem bounds_15_24899 : exactInterval 15 24899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24899 : oddCount 24899 15 = 9 ∧ acceleratedOrbit 15 24899 = 14960 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24899) = 3 ^ 9 * m + 14960 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24899.1, data_15_24899.2]

/-- Complete interval computation for depth 15, residue 24900. -/
theorem bounds_15_24900 : exactInterval 15 24900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24900 : oddCount 24900 15 = 7 ∧ acceleratedOrbit 15 24900 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24900) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24900.1, data_15_24900.2]

/-- Complete interval computation for depth 15, residue 24901. -/
theorem bounds_15_24901 : exactInterval 15 24901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24901 : oddCount 24901 15 = 7 ∧ acceleratedOrbit 15 24901 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24901) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24901.1, data_15_24901.2]

/-- Complete interval computation for depth 15, residue 24902. -/
theorem bounds_15_24902 : exactInterval 15 24902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24902 : oddCount 24902 15 = 7 ∧ acceleratedOrbit 15 24902 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24902) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24902.1, data_15_24902.2]

end Collatz.Research.PassageAtlas.Batch0760
