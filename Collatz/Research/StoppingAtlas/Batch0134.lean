import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0134

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1018. -/
theorem bounds_11_1018 : exactInterval 11 1018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1018 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1018) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1018 : oddCount 1018 11 = 7 ∧ acceleratedOrbit 11 1018 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1018 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1018) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1018.1, data_11_1018.2]

/-- Complete interval computation for depth 11, residue 1019. -/
theorem bounds_11_1019 : exactInterval 11 1019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1019 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1019) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1019 : oddCount 1019 11 = 7 ∧ acceleratedOrbit 11 1019 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1019 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1019) = 3 ^ 7 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1019.1, data_11_1019.2]

/-- Complete interval computation for depth 11, residue 1020. -/
theorem bounds_11_1020 : exactInterval 11 1020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1020 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1020) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1020 : oddCount 1020 11 = 8 ∧ acceleratedOrbit 11 1020 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1020 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1020) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1020.1, data_11_1020.2]

/-- Complete interval computation for depth 11, residue 1021. -/
theorem bounds_11_1021 : exactInterval 11 1021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1021 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1021) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1021 : oddCount 1021 11 = 8 ∧ acceleratedOrbit 11 1021 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1021 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1021) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1021.1, data_11_1021.2]

/-- Complete interval computation for depth 11, residue 1022. -/
theorem bounds_11_1022 : exactInterval 11 1022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1022 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1022) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1022 : oddCount 1022 11 = 9 ∧ acceleratedOrbit 11 1022 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1022 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1022) = 3 ^ 9 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1022.1, data_11_1022.2]

/-- Complete interval computation for depth 11, residue 1023. -/
theorem bounds_11_1023 : exactInterval 11 1023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1023 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1023) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1023 : oddCount 1023 11 = 10 ∧ acceleratedOrbit 11 1023 = 29524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1023 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1023) = 3 ^ 10 * m + 29524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1023.1, data_11_1023.2]

/-- Complete interval computation for depth 11, residue 1024. -/
theorem bounds_11_1024 : exactInterval 11 1024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1024 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1024) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1024 : oddCount 1024 11 = 1 ∧ acceleratedOrbit 11 1024 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1024 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1024) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1024.1, data_11_1024.2]

/-- Complete interval computation for depth 11, residue 1025. -/
theorem bounds_11_1025 : exactInterval 11 1025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1025 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1025) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1025 : oddCount 1025 11 = 5 ∧ acceleratedOrbit 11 1025 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1025 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1025) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1025.1, data_11_1025.2]

/-- Complete interval computation for depth 11, residue 1026. -/
theorem bounds_11_1026 : exactInterval 11 1026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1026 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1026) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1026 : oddCount 1026 11 = 6 ∧ acceleratedOrbit 11 1026 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1026 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1026) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1026.1, data_11_1026.2]

/-- Complete interval computation for depth 11, residue 1027. -/
theorem bounds_11_1027 : exactInterval 11 1027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1027 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1027) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1027 : oddCount 1027 11 = 6 ∧ acceleratedOrbit 11 1027 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1027 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1027) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1027.1, data_11_1027.2]

/-- Complete interval computation for depth 11, residue 1028. -/
theorem bounds_11_1028 : exactInterval 11 1028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1028 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1028) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1028 : oddCount 1028 11 = 4 ∧ acceleratedOrbit 11 1028 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1028 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1028) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1028.1, data_11_1028.2]

/-- Complete interval computation for depth 11, residue 1029. -/
theorem bounds_11_1029 : exactInterval 11 1029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1029 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1029) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1029 : oddCount 1029 11 = 4 ∧ acceleratedOrbit 11 1029 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1029 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1029) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1029.1, data_11_1029.2]

/-- Complete interval computation for depth 11, residue 1030. -/
theorem bounds_11_1030 : exactInterval 11 1030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1030 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1030) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1030 : oddCount 1030 11 = 4 ∧ acceleratedOrbit 11 1030 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1030 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1030) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1030.1, data_11_1030.2]

/-- Complete interval computation for depth 11, residue 1031. -/
theorem bounds_11_1031 : exactInterval 11 1031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1031 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1031) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1031 : oddCount 1031 11 = 6 ∧ acceleratedOrbit 11 1031 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1031 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1031) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1031.1, data_11_1031.2]

/-- Complete interval computation for depth 11, residue 1032. -/
theorem bounds_11_1032 : exactInterval 11 1032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1032 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1032) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1032 : oddCount 1032 11 = 5 ∧ acceleratedOrbit 11 1032 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1032 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1032) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1032.1, data_11_1032.2]

/-- Complete interval computation for depth 11, residue 1033. -/
theorem bounds_11_1033 : exactInterval 11 1033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1033 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1033) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1033 : oddCount 1033 11 = 7 ∧ acceleratedOrbit 11 1033 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1033 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1033) = 3 ^ 7 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1033.1, data_11_1033.2]

end Collatz.Research.StoppingAtlas.Batch0134
