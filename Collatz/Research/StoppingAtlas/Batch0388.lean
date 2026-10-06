import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0388

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2872. -/
theorem bounds_12_2872 : exactInterval 12 2872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2872 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2872) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2872 : oddCount 2872 12 = 8 ∧ acceleratedOrbit 12 2872 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2872 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2872) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2872.1, data_12_2872.2]

/-- Complete interval computation for depth 12, residue 2873. -/
theorem bounds_12_2873 : exactInterval 12 2873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2873 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2873) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2873 : oddCount 2873 12 = 8 ∧ acceleratedOrbit 12 2873 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2873 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2873) = 3 ^ 8 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2873.1, data_12_2873.2]

/-- Complete interval computation for depth 12, residue 2874. -/
theorem bounds_12_2874 : exactInterval 12 2874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2874 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2874) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2874 : oddCount 2874 12 = 8 ∧ acceleratedOrbit 12 2874 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2874 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2874) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2874.1, data_12_2874.2]

/-- Complete interval computation for depth 12, residue 2875. -/
theorem bounds_12_2875 : exactInterval 12 2875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2875 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2875) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2875 : oddCount 2875 12 = 7 ∧ acceleratedOrbit 12 2875 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2875 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2875) = 3 ^ 7 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2875.1, data_12_2875.2]

/-- Complete interval computation for depth 12, residue 2876. -/
theorem bounds_12_2876 : exactInterval 12 2876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2876 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2876) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2876 : oddCount 2876 12 = 8 ∧ acceleratedOrbit 12 2876 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2876 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2876) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2876.1, data_12_2876.2]

/-- Complete interval computation for depth 12, residue 2877. -/
theorem bounds_12_2877 : exactInterval 12 2877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2877 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2877) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2877 : oddCount 2877 12 = 8 ∧ acceleratedOrbit 12 2877 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2877 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2877) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2877.1, data_12_2877.2]

/-- Complete interval computation for depth 12, residue 2878. -/
theorem bounds_12_2878 : exactInterval 12 2878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2878 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2878) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2878 : oddCount 2878 12 = 9 ∧ acceleratedOrbit 12 2878 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2878 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2878) = 3 ^ 9 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2878.1, data_12_2878.2]

/-- Complete interval computation for depth 12, residue 2879. -/
theorem bounds_12_2879 : exactInterval 12 2879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2879 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2879) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2879 : oddCount 2879 12 = 9 ∧ acceleratedOrbit 12 2879 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2879 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2879) = 3 ^ 9 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2879.1, data_12_2879.2]

/-- Complete interval computation for depth 12, residue 2880. -/
theorem bounds_12_2880 : exactInterval 12 2880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2880 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2880) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2880 : oddCount 2880 12 = 3 ∧ acceleratedOrbit 12 2880 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2880 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2880) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2880.1, data_12_2880.2]

/-- Complete interval computation for depth 12, residue 2881. -/
theorem bounds_12_2881 : exactInterval 12 2881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2881 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2881) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2881 : oddCount 2881 12 = 3 ∧ acceleratedOrbit 12 2881 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2881 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2881) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2881.1, data_12_2881.2]

/-- Complete interval computation for depth 12, residue 2882. -/
theorem bounds_12_2882 : exactInterval 12 2882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2882 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2882) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2882 : oddCount 2882 12 = 6 ∧ acceleratedOrbit 12 2882 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2882 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2882) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2882.1, data_12_2882.2]

/-- Complete interval computation for depth 12, residue 2883. -/
theorem bounds_12_2883 : exactInterval 12 2883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2883 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2883) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2883 : oddCount 2883 12 = 6 ∧ acceleratedOrbit 12 2883 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2883 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2883) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2883.1, data_12_2883.2]

/-- Complete interval computation for depth 12, residue 2884. -/
theorem bounds_12_2884 : exactInterval 12 2884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2884 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2884) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2884 : oddCount 2884 12 = 5 ∧ acceleratedOrbit 12 2884 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2884 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2884) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2884.1, data_12_2884.2]

/-- Complete interval computation for depth 12, residue 2885. -/
theorem bounds_12_2885 : exactInterval 12 2885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2885 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2885) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2885 : oddCount 2885 12 = 5 ∧ acceleratedOrbit 12 2885 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2885 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2885) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2885.1, data_12_2885.2]

/-- Complete interval computation for depth 12, residue 2886. -/
theorem bounds_12_2886 : exactInterval 12 2886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2886 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2886) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2886 : oddCount 2886 12 = 5 ∧ acceleratedOrbit 12 2886 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2886 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2886) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2886.1, data_12_2886.2]

end Collatz.Research.StoppingAtlas.Batch0388
