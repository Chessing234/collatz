import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0455

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14876. -/
theorem bounds_15_14876 : exactInterval 15 14876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14876 : oddCount 14876 15 = 7 ∧ acceleratedOrbit 15 14876 = 994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14876) = 3 ^ 7 * m + 994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14876.1, data_15_14876.2]

/-- Complete interval computation for depth 15, residue 14877. -/
theorem bounds_15_14877 : exactInterval 15 14877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14877 : oddCount 14877 15 = 7 ∧ acceleratedOrbit 15 14877 = 994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14877) = 3 ^ 7 * m + 994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14877.1, data_15_14877.2]

/-- Complete interval computation for depth 15, residue 14878. -/
theorem bounds_15_14878 : exactInterval 15 14878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14878 : oddCount 14878 15 = 7 ∧ acceleratedOrbit 15 14878 = 994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14878) = 3 ^ 7 * m + 994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14878.1, data_15_14878.2]

/-- Complete interval computation for depth 15, residue 14879. -/
theorem bounds_15_14879 : exactInterval 15 14879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14879 : oddCount 14879 15 = 9 ∧ acceleratedOrbit 15 14879 = 8939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14879) = 3 ^ 9 * m + 8939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14879.1, data_15_14879.2]

/-- Complete interval computation for depth 15, residue 14880. -/
theorem bounds_15_14880 : exactInterval 15 14880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14880 : oddCount 14880 15 = 4 ∧ acceleratedOrbit 15 14880 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14880) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14880.1, data_15_14880.2]

/-- Complete interval computation for depth 15, residue 14881. -/
theorem bounds_15_14881 : exactInterval 15 14881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14881 : oddCount 14881 15 = 7 ∧ acceleratedOrbit 15 14881 = 994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14881) = 3 ^ 7 * m + 994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14881.1, data_15_14881.2]

/-- Complete interval computation for depth 15, residue 14882. -/
theorem bounds_15_14882 : exactInterval 15 14882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14882 : oddCount 14882 15 = 6 ∧ acceleratedOrbit 15 14882 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14882) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14882.1, data_15_14882.2]

/-- Complete interval computation for depth 15, residue 14883. -/
theorem bounds_15_14883 : exactInterval 15 14883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14883 : oddCount 14883 15 = 6 ∧ acceleratedOrbit 15 14883 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14883) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14883.1, data_15_14883.2]

/-- Complete interval computation for depth 15, residue 14884. -/
theorem bounds_15_14884 : exactInterval 15 14884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14884 : oddCount 14884 15 = 10 ∧ acceleratedOrbit 15 14884 = 26837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14884) = 3 ^ 10 * m + 26837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14884.1, data_15_14884.2]

/-- Complete interval computation for depth 15, residue 14885. -/
theorem bounds_15_14885 : exactInterval 15 14885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14885 : oddCount 14885 15 = 10 ∧ acceleratedOrbit 15 14885 = 26837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14885) = 3 ^ 10 * m + 26837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14885.1, data_15_14885.2]

/-- Complete interval computation for depth 15, residue 14886. -/
theorem bounds_15_14886 : exactInterval 15 14886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14886 : oddCount 14886 15 = 10 ∧ acceleratedOrbit 15 14886 = 26837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14886) = 3 ^ 10 * m + 26837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14886.1, data_15_14886.2]

/-- Complete interval computation for depth 15, residue 14887. -/
theorem bounds_15_14887 : exactInterval 15 14887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14887 : oddCount 14887 15 = 7 ∧ acceleratedOrbit 15 14887 = 994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14887) = 3 ^ 7 * m + 994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14887.1, data_15_14887.2]

/-- Complete interval computation for depth 15, residue 14888. -/
theorem bounds_15_14888 : exactInterval 15 14888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14888 : oddCount 14888 15 = 4 ∧ acceleratedOrbit 15 14888 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14888) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14888.1, data_15_14888.2]

/-- Complete interval computation for depth 15, residue 14889. -/
theorem bounds_15_14889 : exactInterval 15 14889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14889 : oddCount 14889 15 = 9 ∧ acceleratedOrbit 15 14889 = 8945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14889) = 3 ^ 9 * m + 8945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14889.1, data_15_14889.2]

/-- Complete interval computation for depth 15, residue 14890. -/
theorem bounds_15_14890 : exactInterval 15 14890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14890 : oddCount 14890 15 = 4 ∧ acceleratedOrbit 15 14890 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14890) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14890.1, data_15_14890.2]

/-- Complete interval computation for depth 15, residue 14891. -/
theorem bounds_15_14891 : exactInterval 15 14891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14891 : oddCount 14891 15 = 6 ∧ acceleratedOrbit 15 14891 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14891) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14891.1, data_15_14891.2]

/-- Complete interval computation for depth 15, residue 14892. -/
theorem bounds_15_14892 : exactInterval 15 14892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14892 : oddCount 14892 15 = 6 ∧ acceleratedOrbit 15 14892 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14892) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14892.1, data_15_14892.2]

/-- Complete interval computation for depth 15, residue 14893. -/
theorem bounds_15_14893 : exactInterval 15 14893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14893 : oddCount 14893 15 = 6 ∧ acceleratedOrbit 15 14893 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14893) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14893.1, data_15_14893.2]

/-- Complete interval computation for depth 15, residue 14894. -/
theorem bounds_15_14894 : exactInterval 15 14894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14894 : oddCount 14894 15 = 6 ∧ acceleratedOrbit 15 14894 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14894) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14894.1, data_15_14894.2]

/-- Complete interval computation for depth 15, residue 14895. -/
theorem bounds_15_14895 : exactInterval 15 14895 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14895) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14895 : oddCount 14895 15 = 9 ∧ acceleratedOrbit 15 14895 = 8948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14895) = 3 ^ 9 * m + 8948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14895.1, data_15_14895.2]

/-- Complete interval computation for depth 15, residue 14896. -/
theorem bounds_15_14896 : exactInterval 15 14896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14896 : oddCount 14896 15 = 4 ∧ acceleratedOrbit 15 14896 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14896) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14896.1, data_15_14896.2]

/-- Complete interval computation for depth 15, residue 14897. -/
theorem bounds_15_14897 : exactInterval 15 14897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14897 : oddCount 14897 15 = 9 ∧ acceleratedOrbit 15 14897 = 8954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14897) = 3 ^ 9 * m + 8954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14897.1, data_15_14897.2]

/-- Complete interval computation for depth 15, residue 14898. -/
theorem bounds_15_14898 : exactInterval 15 14898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14898 : oddCount 14898 15 = 9 ∧ acceleratedOrbit 15 14898 = 8954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14898) = 3 ^ 9 * m + 8954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14898.1, data_15_14898.2]

/-- Complete interval computation for depth 15, residue 14899. -/
theorem bounds_15_14899 : exactInterval 15 14899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14899 : oddCount 14899 15 = 9 ∧ acceleratedOrbit 15 14899 = 8954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14899) = 3 ^ 9 * m + 8954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14899.1, data_15_14899.2]

/-- Complete interval computation for depth 15, residue 14900. -/
theorem bounds_15_14900 : exactInterval 15 14900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14900 : oddCount 14900 15 = 4 ∧ acceleratedOrbit 15 14900 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14900) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14900.1, data_15_14900.2]

/-- Complete interval computation for depth 15, residue 14901. -/
theorem bounds_15_14901 : exactInterval 15 14901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14901 : oddCount 14901 15 = 4 ∧ acceleratedOrbit 15 14901 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14901) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14901.1, data_15_14901.2]

/-- Complete interval computation for depth 15, residue 14902. -/
theorem bounds_15_14902 : exactInterval 15 14902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14902 : oddCount 14902 15 = 9 ∧ acceleratedOrbit 15 14902 = 8953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14902) = 3 ^ 9 * m + 8953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14902.1, data_15_14902.2]

/-- Complete interval computation for depth 15, residue 14903. -/
theorem bounds_15_14903 : exactInterval 15 14903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14903 : oddCount 14903 15 = 9 ∧ acceleratedOrbit 15 14903 = 8953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14903) = 3 ^ 9 * m + 8953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14903.1, data_15_14903.2]

/-- Complete interval computation for depth 15, residue 14904. -/
theorem bounds_15_14904 : exactInterval 15 14904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14904 : oddCount 14904 15 = 8 ∧ acceleratedOrbit 15 14904 = 2987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14904) = 3 ^ 8 * m + 2987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14904.1, data_15_14904.2]

/-- Complete interval computation for depth 15, residue 14905. -/
theorem bounds_15_14905 : exactInterval 15 14905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14905 : oddCount 14905 15 = 7 ∧ acceleratedOrbit 15 14905 = 995 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14905) = 3 ^ 7 * m + 995 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14905.1, data_15_14905.2]

/-- Complete interval computation for depth 15, residue 14906. -/
theorem bounds_15_14906 : exactInterval 15 14906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14906 : oddCount 14906 15 = 8 ∧ acceleratedOrbit 15 14906 = 2987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14906) = 3 ^ 8 * m + 2987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14906.1, data_15_14906.2]

/-- Complete interval computation for depth 15, residue 14907. -/
theorem bounds_15_14907 : exactInterval 15 14907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14907 : oddCount 14907 15 = 8 ∧ acceleratedOrbit 15 14907 = 2987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14907) = 3 ^ 8 * m + 2987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14907.1, data_15_14907.2]

/-- Complete interval computation for depth 15, residue 14908. -/
theorem bounds_15_14908 : exactInterval 15 14908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14908 : oddCount 14908 15 = 8 ∧ acceleratedOrbit 15 14908 = 2987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14908) = 3 ^ 8 * m + 2987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14908.1, data_15_14908.2]

end Collatz.Research.PassageAtlas.Batch0455
