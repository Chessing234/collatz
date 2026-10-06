import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0534

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1018. -/
theorem bounds_13_1018 : exactInterval 13 1018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1018 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1018) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1018 : oddCount 1018 13 = 8 ∧ acceleratedOrbit 13 1018 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1018 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1018) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1018.1, data_13_1018.2]

/-- Complete interval computation for depth 13, residue 1019. -/
theorem bounds_13_1019 : exactInterval 13 1019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1019 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1019) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1019 : oddCount 1019 13 = 8 ∧ acceleratedOrbit 13 1019 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1019 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1019) = 3 ^ 8 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1019.1, data_13_1019.2]

/-- Complete interval computation for depth 13, residue 1020. -/
theorem bounds_13_1020 : exactInterval 13 1020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1020 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1020) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1020 : oddCount 1020 13 = 8 ∧ acceleratedOrbit 13 1020 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1020 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1020) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1020.1, data_13_1020.2]

/-- Complete interval computation for depth 13, residue 1021. -/
theorem bounds_13_1021 : exactInterval 13 1021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1021 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1021) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1021 : oddCount 1021 13 = 8 ∧ acceleratedOrbit 13 1021 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1021 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1021) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1021.1, data_13_1021.2]

/-- Complete interval computation for depth 13, residue 1022. -/
theorem bounds_13_1022 : exactInterval 13 1022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1022 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1022) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1022 : oddCount 1022 13 = 10 ∧ acceleratedOrbit 13 1022 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1022 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1022) = 3 ^ 10 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1022.1, data_13_1022.2]

/-- Complete interval computation for depth 13, residue 1023. -/
theorem bounds_13_1023 : exactInterval 13 1023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1023 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1023) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1023 : oddCount 1023 13 = 10 ∧ acceleratedOrbit 13 1023 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1023 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1023) = 3 ^ 10 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1023.1, data_13_1023.2]

/-- Complete interval computation for depth 13, residue 1024. -/
theorem bounds_13_1024 : exactInterval 13 1024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1024 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1024) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1024 : oddCount 1024 13 = 2 ∧ acceleratedOrbit 13 1024 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1024 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1024) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1024.1, data_13_1024.2]

/-- Complete interval computation for depth 13, residue 1025. -/
theorem bounds_13_1025 : exactInterval 13 1025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1025 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1025) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1025 : oddCount 1025 13 = 6 ∧ acceleratedOrbit 13 1025 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1025 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1025) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1025.1, data_13_1025.2]

/-- Complete interval computation for depth 13, residue 1026. -/
theorem bounds_13_1026 : exactInterval 13 1026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1026 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1026) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1026 : oddCount 1026 13 = 6 ∧ acceleratedOrbit 13 1026 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1026 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1026) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1026.1, data_13_1026.2]

/-- Complete interval computation for depth 13, residue 1027. -/
theorem bounds_13_1027 : exactInterval 13 1027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1027 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1027) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1027 : oddCount 1027 13 = 6 ∧ acceleratedOrbit 13 1027 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1027 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1027) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1027.1, data_13_1027.2]

/-- Complete interval computation for depth 13, residue 1028. -/
theorem bounds_13_1028 : exactInterval 13 1028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1028 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1028) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1028 : oddCount 1028 13 = 5 ∧ acceleratedOrbit 13 1028 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1028 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1028) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1028.1, data_13_1028.2]

/-- Complete interval computation for depth 13, residue 1029. -/
theorem bounds_13_1029 : exactInterval 13 1029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1029 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1029) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1029 : oddCount 1029 13 = 5 ∧ acceleratedOrbit 13 1029 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1029 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1029) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1029.1, data_13_1029.2]

/-- Complete interval computation for depth 13, residue 1030. -/
theorem bounds_13_1030 : exactInterval 13 1030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1030 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1030) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1030 : oddCount 1030 13 = 5 ∧ acceleratedOrbit 13 1030 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1030 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1030) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1030.1, data_13_1030.2]

/-- Complete interval computation for depth 13, residue 1031. -/
theorem bounds_13_1031 : exactInterval 13 1031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1031 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1031) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1031 : oddCount 1031 13 = 6 ∧ acceleratedOrbit 13 1031 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1031 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1031) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1031.1, data_13_1031.2]

/-- Complete interval computation for depth 13, residue 1032. -/
theorem bounds_13_1032 : exactInterval 13 1032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1032 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1032) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1032 : oddCount 1032 13 = 6 ∧ acceleratedOrbit 13 1032 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1032 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1032) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1032.1, data_13_1032.2]

/-- Complete interval computation for depth 13, residue 1033. -/
theorem bounds_13_1033 : exactInterval 13 1033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1033 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1033) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1033 : oddCount 1033 13 = 8 ∧ acceleratedOrbit 13 1033 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1033 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1033) = 3 ^ 8 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1033.1, data_13_1033.2]

end Collatz.Research.StoppingAtlas.Batch0534
