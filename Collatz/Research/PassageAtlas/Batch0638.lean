import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0638

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20873. -/
theorem bounds_15_20873 : exactInterval 15 20873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20873 : oddCount 20873 15 = 8 ∧ acceleratedOrbit 15 20873 = 4180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20873) = 3 ^ 8 * m + 4180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20873.1, data_15_20873.2]

/-- Complete interval computation for depth 15, residue 20874. -/
theorem bounds_15_20874 : exactInterval 15 20874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20874 : oddCount 20874 15 = 7 ∧ acceleratedOrbit 15 20874 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20874) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20874.1, data_15_20874.2]

/-- Complete interval computation for depth 15, residue 20875. -/
theorem bounds_15_20875 : exactInterval 15 20875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20875 : oddCount 20875 15 = 10 ∧ acceleratedOrbit 15 20875 = 37624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20875) = 3 ^ 10 * m + 37624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20875.1, data_15_20875.2]

/-- Complete interval computation for depth 15, residue 20876. -/
theorem bounds_15_20876 : exactInterval 15 20876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20876 : oddCount 20876 15 = 7 ∧ acceleratedOrbit 15 20876 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20876) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20876.1, data_15_20876.2]

/-- Complete interval computation for depth 15, residue 20877. -/
theorem bounds_15_20877 : exactInterval 15 20877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20877 : oddCount 20877 15 = 7 ∧ acceleratedOrbit 15 20877 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20877) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20877.1, data_15_20877.2]

/-- Complete interval computation for depth 15, residue 20878. -/
theorem bounds_15_20878 : exactInterval 15 20878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20878 : oddCount 20878 15 = 9 ∧ acceleratedOrbit 15 20878 = 12545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20878) = 3 ^ 9 * m + 12545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20878.1, data_15_20878.2]

/-- Complete interval computation for depth 15, residue 20879. -/
theorem bounds_15_20879 : exactInterval 15 20879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20879 : oddCount 20879 15 = 9 ∧ acceleratedOrbit 15 20879 = 12545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20879) = 3 ^ 9 * m + 12545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20879.1, data_15_20879.2]

/-- Complete interval computation for depth 15, residue 20880. -/
theorem bounds_15_20880 : exactInterval 15 20880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20880 : oddCount 20880 15 = 7 ∧ acceleratedOrbit 15 20880 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20880) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20880.1, data_15_20880.2]

/-- Complete interval computation for depth 15, residue 20881. -/
theorem bounds_15_20881 : exactInterval 15 20881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20881 : oddCount 20881 15 = 5 ∧ acceleratedOrbit 15 20881 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20881) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20881.1, data_15_20881.2]

/-- Complete interval computation for depth 15, residue 20882. -/
theorem bounds_15_20882 : exactInterval 15 20882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20882 : oddCount 20882 15 = 5 ∧ acceleratedOrbit 15 20882 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20882) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20882.1, data_15_20882.2]

/-- Complete interval computation for depth 15, residue 20883. -/
theorem bounds_15_20883 : exactInterval 15 20883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20883 : oddCount 20883 15 = 5 ∧ acceleratedOrbit 15 20883 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20883) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20883.1, data_15_20883.2]

/-- Complete interval computation for depth 15, residue 20884. -/
theorem bounds_15_20884 : exactInterval 15 20884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20884 : oddCount 20884 15 = 7 ∧ acceleratedOrbit 15 20884 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20884) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20884.1, data_15_20884.2]

/-- Complete interval computation for depth 15, residue 20885. -/
theorem bounds_15_20885 : exactInterval 15 20885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20885 : oddCount 20885 15 = 7 ∧ acceleratedOrbit 15 20885 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20885) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20885.1, data_15_20885.2]

/-- Complete interval computation for depth 15, residue 20886. -/
theorem bounds_15_20886 : exactInterval 15 20886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20886 : oddCount 20886 15 = 9 ∧ acceleratedOrbit 15 20886 = 12554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20886) = 3 ^ 9 * m + 12554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20886.1, data_15_20886.2]

/-- Complete interval computation for depth 15, residue 20887. -/
theorem bounds_15_20887 : exactInterval 15 20887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20887 : oddCount 20887 15 = 9 ∧ acceleratedOrbit 15 20887 = 12554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20887) = 3 ^ 9 * m + 12554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20887.1, data_15_20887.2]

/-- Complete interval computation for depth 15, residue 20888. -/
theorem bounds_15_20888 : exactInterval 15 20888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20888 : oddCount 20888 15 = 7 ∧ acceleratedOrbit 15 20888 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20888) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20888.1, data_15_20888.2]

/-- Complete interval computation for depth 15, residue 20889. -/
theorem bounds_15_20889 : exactInterval 15 20889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20889 : oddCount 20889 15 = 9 ∧ acceleratedOrbit 15 20889 = 12554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20889) = 3 ^ 9 * m + 12554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20889.1, data_15_20889.2]

/-- Complete interval computation for depth 15, residue 20890. -/
theorem bounds_15_20890 : exactInterval 15 20890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20890 : oddCount 20890 15 = 7 ∧ acceleratedOrbit 15 20890 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20890) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20890.1, data_15_20890.2]

/-- Complete interval computation for depth 15, residue 20891. -/
theorem bounds_15_20891 : exactInterval 15 20891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20891 : oddCount 20891 15 = 9 ∧ acceleratedOrbit 15 20891 = 12550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20891) = 3 ^ 9 * m + 12550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20891.1, data_15_20891.2]

/-- Complete interval computation for depth 15, residue 20892. -/
theorem bounds_15_20892 : exactInterval 15 20892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20892 : oddCount 20892 15 = 10 ∧ acceleratedOrbit 15 20892 = 37658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20892) = 3 ^ 10 * m + 37658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20892.1, data_15_20892.2]

/-- Complete interval computation for depth 15, residue 20893. -/
theorem bounds_15_20893 : exactInterval 15 20893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20893 : oddCount 20893 15 = 10 ∧ acceleratedOrbit 15 20893 = 37658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20893) = 3 ^ 10 * m + 37658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20893.1, data_15_20893.2]

/-- Complete interval computation for depth 15, residue 20894. -/
theorem bounds_15_20894 : exactInterval 15 20894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20894 : oddCount 20894 15 = 10 ∧ acceleratedOrbit 15 20894 = 37658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20894) = 3 ^ 10 * m + 37658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20894.1, data_15_20894.2]

/-- Complete interval computation for depth 15, residue 20895. -/
theorem bounds_15_20895 : exactInterval 15 20895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20895 : oddCount 20895 15 = 12 ∧ acceleratedOrbit 15 20895 = 338903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20895) = 3 ^ 12 * m + 338903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20895.1, data_15_20895.2]

/-- Complete interval computation for depth 15, residue 20896. -/
theorem bounds_15_20896 : exactInterval 15 20896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20896 : oddCount 20896 15 = 4 ∧ acceleratedOrbit 15 20896 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20896) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20896.1, data_15_20896.2]

/-- Complete interval computation for depth 15, residue 20897. -/
theorem bounds_15_20897 : exactInterval 15 20897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20897 : oddCount 20897 15 = 11 ∧ acceleratedOrbit 15 20897 = 112994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20897) = 3 ^ 11 * m + 112994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20897.1, data_15_20897.2]

/-- Complete interval computation for depth 15, residue 20898. -/
theorem bounds_15_20898 : exactInterval 15 20898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20898 : oddCount 20898 15 = 8 ∧ acceleratedOrbit 15 20898 = 4187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20898) = 3 ^ 8 * m + 4187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20898.1, data_15_20898.2]

/-- Complete interval computation for depth 15, residue 20899. -/
theorem bounds_15_20899 : exactInterval 15 20899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20899 : oddCount 20899 15 = 8 ∧ acceleratedOrbit 15 20899 = 4187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20899) = 3 ^ 8 * m + 4187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20899.1, data_15_20899.2]

/-- Complete interval computation for depth 15, residue 20900. -/
theorem bounds_15_20900 : exactInterval 15 20900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20900 : oddCount 20900 15 = 8 ∧ acceleratedOrbit 15 20900 = 4187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20900) = 3 ^ 8 * m + 4187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20900.1, data_15_20900.2]

/-- Complete interval computation for depth 15, residue 20901. -/
theorem bounds_15_20901 : exactInterval 15 20901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20901 : oddCount 20901 15 = 8 ∧ acceleratedOrbit 15 20901 = 4187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20901) = 3 ^ 8 * m + 4187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20901.1, data_15_20901.2]

/-- Complete interval computation for depth 15, residue 20902. -/
theorem bounds_15_20902 : exactInterval 15 20902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20902 : oddCount 20902 15 = 8 ∧ acceleratedOrbit 15 20902 = 4187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20902) = 3 ^ 8 * m + 4187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20902.1, data_15_20902.2]

/-- Complete interval computation for depth 15, residue 20903. -/
theorem bounds_15_20903 : exactInterval 15 20903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20903 : oddCount 20903 15 = 8 ∧ acceleratedOrbit 15 20903 = 4186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20903) = 3 ^ 8 * m + 4186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20903.1, data_15_20903.2]

/-- Complete interval computation for depth 15, residue 20904. -/
theorem bounds_15_20904 : exactInterval 15 20904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20904 : oddCount 20904 15 = 4 ∧ acceleratedOrbit 15 20904 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20904) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20904.1, data_15_20904.2]

end Collatz.Research.PassageAtlas.Batch0638
