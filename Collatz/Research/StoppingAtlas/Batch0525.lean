import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0525

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 880. -/
theorem bounds_13_880 : exactInterval 13 880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_880 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 880) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_880 : oddCount 880 13 = 7 ∧ acceleratedOrbit 13 880 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_880 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 880) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_880.1, data_13_880.2]

/-- Complete interval computation for depth 13, residue 881. -/
theorem bounds_13_881 : exactInterval 13 881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_881 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 881) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_881 : oddCount 881 13 = 7 ∧ acceleratedOrbit 13 881 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_881 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 881) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_881.1, data_13_881.2]

/-- Complete interval computation for depth 13, residue 882. -/
theorem bounds_13_882 : exactInterval 13 882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_882 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 882) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_882 : oddCount 882 13 = 6 ∧ acceleratedOrbit 13 882 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_882 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 882) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_882.1, data_13_882.2]

/-- Complete interval computation for depth 13, residue 883. -/
theorem bounds_13_883 : exactInterval 13 883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_883 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 883) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_883 : oddCount 883 13 = 6 ∧ acceleratedOrbit 13 883 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_883 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 883) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_883.1, data_13_883.2]

/-- Complete interval computation for depth 13, residue 884. -/
theorem bounds_13_884 : exactInterval 13 884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_884 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 884) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_884 : oddCount 884 13 = 7 ∧ acceleratedOrbit 13 884 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_884 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 884) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_884.1, data_13_884.2]

/-- Complete interval computation for depth 13, residue 885. -/
theorem bounds_13_885 : exactInterval 13 885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_885 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 885) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_885 : oddCount 885 13 = 7 ∧ acceleratedOrbit 13 885 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_885 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 885) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_885.1, data_13_885.2]

/-- Complete interval computation for depth 13, residue 886. -/
theorem bounds_13_886 : exactInterval 13 886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_886 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 886) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_886 : oddCount 886 13 = 7 ∧ acceleratedOrbit 13 886 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_886 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 886) = 3 ^ 7 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_886.1, data_13_886.2]

/-- Complete interval computation for depth 13, residue 887. -/
theorem bounds_13_887 : exactInterval 13 887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_887 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 887) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_887 : oddCount 887 13 = 7 ∧ acceleratedOrbit 13 887 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_887 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 887) = 3 ^ 7 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_887.1, data_13_887.2]

/-- Complete interval computation for depth 13, residue 888. -/
theorem bounds_13_888 : exactInterval 13 888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_888 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 888) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_888 : oddCount 888 13 = 8 ∧ acceleratedOrbit 13 888 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_888 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 888) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_888.1, data_13_888.2]

/-- Complete interval computation for depth 13, residue 889. -/
theorem bounds_13_889 : exactInterval 13 889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_889 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 889) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_889 : oddCount 889 13 = 10 ∧ acceleratedOrbit 13 889 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_889 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 889) = 3 ^ 10 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_889.1, data_13_889.2]

/-- Complete interval computation for depth 13, residue 890. -/
theorem bounds_13_890 : exactInterval 13 890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_890 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 890) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_890 : oddCount 890 13 = 8 ∧ acceleratedOrbit 13 890 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_890 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 890) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_890.1, data_13_890.2]

/-- Complete interval computation for depth 13, residue 891. -/
theorem bounds_13_891 : exactInterval 13 891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_891 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 891) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_891 : oddCount 891 13 = 9 ∧ acceleratedOrbit 13 891 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_891 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 891) = 3 ^ 9 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_891.1, data_13_891.2]

/-- Complete interval computation for depth 13, residue 892. -/
theorem bounds_13_892 : exactInterval 13 892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_892 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 892) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_892 : oddCount 892 13 = 8 ∧ acceleratedOrbit 13 892 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_892 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 892) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_892.1, data_13_892.2]

/-- Complete interval computation for depth 13, residue 893. -/
theorem bounds_13_893 : exactInterval 13 893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_893 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 893) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_893 : oddCount 893 13 = 8 ∧ acceleratedOrbit 13 893 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_893 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 893) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_893.1, data_13_893.2]

/-- Complete interval computation for depth 13, residue 894. -/
theorem bounds_13_894 : exactInterval 13 894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_894 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 894) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_894 : oddCount 894 13 = 9 ∧ acceleratedOrbit 13 894 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_894 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 894) = 3 ^ 9 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_894.1, data_13_894.2]

/-- Complete interval computation for depth 13, residue 895. -/
theorem bounds_13_895 : exactInterval 13 895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_895 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 895) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_895 : oddCount 895 13 = 9 ∧ acceleratedOrbit 13 895 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_895 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 895) = 3 ^ 9 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_895.1, data_13_895.2]

end Collatz.Research.StoppingAtlas.Batch0525
