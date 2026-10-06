import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0125

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 880. -/
theorem bounds_11_880 : exactInterval 11 880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_880 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 880) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_880 : oddCount 880 11 = 5 ∧ acceleratedOrbit 11 880 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_880 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 880) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_880.1, data_11_880.2]

/-- Complete interval computation for depth 11, residue 881. -/
theorem bounds_11_881 : exactInterval 11 881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_881 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 881) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_881 : oddCount 881 11 = 5 ∧ acceleratedOrbit 11 881 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_881 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 881) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_881.1, data_11_881.2]

/-- Complete interval computation for depth 11, residue 882. -/
theorem bounds_11_882 : exactInterval 11 882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_882 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 882) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_882 : oddCount 882 11 = 4 ∧ acceleratedOrbit 11 882 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_882 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 882) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_882.1, data_11_882.2]

/-- Complete interval computation for depth 11, residue 883. -/
theorem bounds_11_883 : exactInterval 11 883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_883 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 883) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_883 : oddCount 883 11 = 4 ∧ acceleratedOrbit 11 883 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_883 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 883) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_883.1, data_11_883.2]

/-- Complete interval computation for depth 11, residue 884. -/
theorem bounds_11_884 : exactInterval 11 884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_884 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 884) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_884 : oddCount 884 11 = 5 ∧ acceleratedOrbit 11 884 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_884 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 884) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_884.1, data_11_884.2]

/-- Complete interval computation for depth 11, residue 885. -/
theorem bounds_11_885 : exactInterval 11 885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_885 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 885) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_885 : oddCount 885 11 = 5 ∧ acceleratedOrbit 11 885 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_885 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 885) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_885.1, data_11_885.2]

/-- Complete interval computation for depth 11, residue 886. -/
theorem bounds_11_886 : exactInterval 11 886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_886 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 886) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_886 : oddCount 886 11 = 6 ∧ acceleratedOrbit 11 886 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_886 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 886) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_886.1, data_11_886.2]

/-- Complete interval computation for depth 11, residue 887. -/
theorem bounds_11_887 : exactInterval 11 887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_887 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 887) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_887 : oddCount 887 11 = 6 ∧ acceleratedOrbit 11 887 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_887 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 887) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_887.1, data_11_887.2]

/-- Complete interval computation for depth 11, residue 888. -/
theorem bounds_11_888 : exactInterval 11 888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_888 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 888) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_888 : oddCount 888 11 = 6 ∧ acceleratedOrbit 11 888 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_888 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 888) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_888.1, data_11_888.2]

/-- Complete interval computation for depth 11, residue 889. -/
theorem bounds_11_889 : exactInterval 11 889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_889 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 889) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_889 : oddCount 889 11 = 8 ∧ acceleratedOrbit 11 889 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_889 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 889) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_889.1, data_11_889.2]

/-- Complete interval computation for depth 11, residue 890. -/
theorem bounds_11_890 : exactInterval 11 890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_890 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 890) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_890 : oddCount 890 11 = 6 ∧ acceleratedOrbit 11 890 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_890 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 890) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_890.1, data_11_890.2]

/-- Complete interval computation for depth 11, residue 891. -/
theorem bounds_11_891 : exactInterval 11 891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_891 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 891) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_891 : oddCount 891 11 = 8 ∧ acceleratedOrbit 11 891 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_891 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 891) = 3 ^ 8 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_891.1, data_11_891.2]

/-- Complete interval computation for depth 11, residue 892. -/
theorem bounds_11_892 : exactInterval 11 892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_892 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 892) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_892 : oddCount 892 11 = 6 ∧ acceleratedOrbit 11 892 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_892 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 892) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_892.1, data_11_892.2]

/-- Complete interval computation for depth 11, residue 893. -/
theorem bounds_11_893 : exactInterval 11 893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_893 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 893) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_893 : oddCount 893 11 = 6 ∧ acceleratedOrbit 11 893 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_893 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 893) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_893.1, data_11_893.2]

/-- Complete interval computation for depth 11, residue 894. -/
theorem bounds_11_894 : exactInterval 11 894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_894 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 894) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_894 : oddCount 894 11 = 9 ∧ acceleratedOrbit 11 894 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_894 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 894) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_894.1, data_11_894.2]

/-- Complete interval computation for depth 11, residue 895. -/
theorem bounds_11_895 : exactInterval 11 895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_895 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 895) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_895 : oddCount 895 11 = 9 ∧ acceleratedOrbit 11 895 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_895 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 895) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_895.1, data_11_895.2]

end Collatz.Research.StoppingAtlas.Batch0125
