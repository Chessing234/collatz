import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0699

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22872. -/
theorem bounds_15_22872 : exactInterval 15 22872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22872 : oddCount 22872 15 = 7 ∧ acceleratedOrbit 15 22872 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22872) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22872.1, data_15_22872.2]

/-- Complete interval computation for depth 15, residue 22873. -/
theorem bounds_15_22873 : exactInterval 15 22873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22873 : oddCount 22873 15 = 6 ∧ acceleratedOrbit 15 22873 = 509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22873) = 3 ^ 6 * m + 509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22873.1, data_15_22873.2]

/-- Complete interval computation for depth 15, residue 22874. -/
theorem bounds_15_22874 : exactInterval 15 22874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22874 : oddCount 22874 15 = 7 ∧ acceleratedOrbit 15 22874 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22874) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22874.1, data_15_22874.2]

/-- Complete interval computation for depth 15, residue 22875. -/
theorem bounds_15_22875 : exactInterval 15 22875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22875 : oddCount 22875 15 = 10 ∧ acceleratedOrbit 15 22875 = 41228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22875) = 3 ^ 10 * m + 41228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22875.1, data_15_22875.2]

/-- Complete interval computation for depth 15, residue 22876. -/
theorem bounds_15_22876 : exactInterval 15 22876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22876 : oddCount 22876 15 = 7 ∧ acceleratedOrbit 15 22876 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22876) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22876.1, data_15_22876.2]

/-- Complete interval computation for depth 15, residue 22877. -/
theorem bounds_15_22877 : exactInterval 15 22877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22877 : oddCount 22877 15 = 7 ∧ acceleratedOrbit 15 22877 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22877) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22877.1, data_15_22877.2]

/-- Complete interval computation for depth 15, residue 22878. -/
theorem bounds_15_22878 : exactInterval 15 22878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22878 : oddCount 22878 15 = 9 ∧ acceleratedOrbit 15 22878 = 13745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22878) = 3 ^ 9 * m + 13745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22878.1, data_15_22878.2]

/-- Complete interval computation for depth 15, residue 22879. -/
theorem bounds_15_22879 : exactInterval 15 22879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22879 : oddCount 22879 15 = 9 ∧ acceleratedOrbit 15 22879 = 13745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22879) = 3 ^ 9 * m + 13745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22879.1, data_15_22879.2]

/-- Complete interval computation for depth 15, residue 22880. -/
theorem bounds_15_22880 : exactInterval 15 22880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22880 : oddCount 22880 15 = 6 ∧ acceleratedOrbit 15 22880 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22880) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22880.1, data_15_22880.2]

/-- Complete interval computation for depth 15, residue 22881. -/
theorem bounds_15_22881 : exactInterval 15 22881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22881 : oddCount 22881 15 = 8 ∧ acceleratedOrbit 15 22881 = 4582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22881) = 3 ^ 8 * m + 4582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22881.1, data_15_22881.2]

/-- Complete interval computation for depth 15, residue 22882. -/
theorem bounds_15_22882 : exactInterval 15 22882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22882 : oddCount 22882 15 = 7 ∧ acceleratedOrbit 15 22882 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22882) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22882.1, data_15_22882.2]

/-- Complete interval computation for depth 15, residue 22883. -/
theorem bounds_15_22883 : exactInterval 15 22883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22883 : oddCount 22883 15 = 7 ∧ acceleratedOrbit 15 22883 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22883) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22883.1, data_15_22883.2]

/-- Complete interval computation for depth 15, residue 22884. -/
theorem bounds_15_22884 : exactInterval 15 22884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22884 : oddCount 22884 15 = 7 ∧ acceleratedOrbit 15 22884 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22884) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22884.1, data_15_22884.2]

/-- Complete interval computation for depth 15, residue 22885. -/
theorem bounds_15_22885 : exactInterval 15 22885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22885 : oddCount 22885 15 = 7 ∧ acceleratedOrbit 15 22885 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22885) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22885.1, data_15_22885.2]

/-- Complete interval computation for depth 15, residue 22886. -/
theorem bounds_15_22886 : exactInterval 15 22886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22886 : oddCount 22886 15 = 7 ∧ acceleratedOrbit 15 22886 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22886) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22886.1, data_15_22886.2]

/-- Complete interval computation for depth 15, residue 22887. -/
theorem bounds_15_22887 : exactInterval 15 22887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22887 : oddCount 22887 15 = 10 ∧ acceleratedOrbit 15 22887 = 41246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22887) = 3 ^ 10 * m + 41246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22887.1, data_15_22887.2]

/-- Complete interval computation for depth 15, residue 22888. -/
theorem bounds_15_22888 : exactInterval 15 22888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22888 : oddCount 22888 15 = 6 ∧ acceleratedOrbit 15 22888 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22888) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22888.1, data_15_22888.2]

/-- Complete interval computation for depth 15, residue 22889. -/
theorem bounds_15_22889 : exactInterval 15 22889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22889 : oddCount 22889 15 = 7 ∧ acceleratedOrbit 15 22889 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22889) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22889.1, data_15_22889.2]

/-- Complete interval computation for depth 15, residue 22890. -/
theorem bounds_15_22890 : exactInterval 15 22890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22890 : oddCount 22890 15 = 6 ∧ acceleratedOrbit 15 22890 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22890) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22890.1, data_15_22890.2]

/-- Complete interval computation for depth 15, residue 22891. -/
theorem bounds_15_22891 : exactInterval 15 22891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22891 : oddCount 22891 15 = 7 ∧ acceleratedOrbit 15 22891 = 1528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22891) = 3 ^ 7 * m + 1528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22891.1, data_15_22891.2]

/-- Complete interval computation for depth 15, residue 22892. -/
theorem bounds_15_22892 : exactInterval 15 22892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22892 : oddCount 22892 15 = 8 ∧ acceleratedOrbit 15 22892 = 4585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22892) = 3 ^ 8 * m + 4585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22892.1, data_15_22892.2]

/-- Complete interval computation for depth 15, residue 22893. -/
theorem bounds_15_22893 : exactInterval 15 22893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22893 : oddCount 22893 15 = 8 ∧ acceleratedOrbit 15 22893 = 4585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22893) = 3 ^ 8 * m + 4585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22893.1, data_15_22893.2]

/-- Complete interval computation for depth 15, residue 22894. -/
theorem bounds_15_22894 : exactInterval 15 22894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22894 : oddCount 22894 15 = 8 ∧ acceleratedOrbit 15 22894 = 4585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22894) = 3 ^ 8 * m + 4585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22894.1, data_15_22894.2]

/-- Complete interval computation for depth 15, residue 22895. -/
theorem bounds_15_22895 : exactInterval 15 22895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22895 : oddCount 22895 15 = 8 ∧ acceleratedOrbit 15 22895 = 4585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22895) = 3 ^ 8 * m + 4585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22895.1, data_15_22895.2]

/-- Complete interval computation for depth 15, residue 22896. -/
theorem bounds_15_22896 : exactInterval 15 22896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22896 : oddCount 22896 15 = 6 ∧ acceleratedOrbit 15 22896 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22896) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22896.1, data_15_22896.2]

/-- Complete interval computation for depth 15, residue 22897. -/
theorem bounds_15_22897 : exactInterval 15 22897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22897 : oddCount 22897 15 = 6 ∧ acceleratedOrbit 15 22897 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22897) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22897.1, data_15_22897.2]

/-- Complete interval computation for depth 15, residue 22898. -/
theorem bounds_15_22898 : exactInterval 15 22898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22898 : oddCount 22898 15 = 9 ∧ acceleratedOrbit 15 22898 = 13760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22898) = 3 ^ 9 * m + 13760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22898.1, data_15_22898.2]

/-- Complete interval computation for depth 15, residue 22899. -/
theorem bounds_15_22899 : exactInterval 15 22899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22899 : oddCount 22899 15 = 9 ∧ acceleratedOrbit 15 22899 = 13760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22899) = 3 ^ 9 * m + 13760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22899.1, data_15_22899.2]

/-- Complete interval computation for depth 15, residue 22900. -/
theorem bounds_15_22900 : exactInterval 15 22900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22900 : oddCount 22900 15 = 6 ∧ acceleratedOrbit 15 22900 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22900) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22900.1, data_15_22900.2]

/-- Complete interval computation for depth 15, residue 22901. -/
theorem bounds_15_22901 : exactInterval 15 22901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22901 : oddCount 22901 15 = 6 ∧ acceleratedOrbit 15 22901 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22901) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22901.1, data_15_22901.2]

/-- Complete interval computation for depth 15, residue 22902. -/
theorem bounds_15_22902 : exactInterval 15 22902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22902 : oddCount 22902 15 = 9 ∧ acceleratedOrbit 15 22902 = 13760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22902) = 3 ^ 9 * m + 13760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22902.1, data_15_22902.2]

/-- Complete interval computation for depth 15, residue 22903. -/
theorem bounds_15_22903 : exactInterval 15 22903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22903 : oddCount 22903 15 = 9 ∧ acceleratedOrbit 15 22903 = 13760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22903) = 3 ^ 9 * m + 13760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22903.1, data_15_22903.2]

end Collatz.Research.PassageAtlas.Batch0699
