import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0032

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1015. -/
theorem bounds_15_1015 : exactInterval 15 1015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1015 : oddCount 1015 15 = 7 ∧ acceleratedOrbit 15 1015 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1015) = 3 ^ 7 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1015.1, data_15_1015.2]

/-- Complete interval computation for depth 15, residue 1016. -/
theorem bounds_15_1016 : exactInterval 15 1016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1016 : oddCount 1016 15 = 8 ∧ acceleratedOrbit 15 1016 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1016) = 3 ^ 8 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1016.1, data_15_1016.2]

/-- Complete interval computation for depth 15, residue 1017. -/
theorem bounds_15_1017 : exactInterval 15 1017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1017 : oddCount 1017 15 = 10 ∧ acceleratedOrbit 15 1017 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1017) = 3 ^ 10 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1017.1, data_15_1017.2]

/-- Complete interval computation for depth 15, residue 1018. -/
theorem bounds_15_1018 : exactInterval 15 1018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1018 : oddCount 1018 15 = 8 ∧ acceleratedOrbit 15 1018 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1018) = 3 ^ 8 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1018.1, data_15_1018.2]

/-- Complete interval computation for depth 15, residue 1019. -/
theorem bounds_15_1019 : exactInterval 15 1019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1019 : oddCount 1019 15 = 9 ∧ acceleratedOrbit 15 1019 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1019) = 3 ^ 9 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1019.1, data_15_1019.2]

/-- Complete interval computation for depth 15, residue 1020. -/
theorem bounds_15_1020 : exactInterval 15 1020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1020 : oddCount 1020 15 = 8 ∧ acceleratedOrbit 15 1020 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1020) = 3 ^ 8 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1020.1, data_15_1020.2]

/-- Complete interval computation for depth 15, residue 1021. -/
theorem bounds_15_1021 : exactInterval 15 1021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1021 : oddCount 1021 15 = 8 ∧ acceleratedOrbit 15 1021 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1021) = 3 ^ 8 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1021.1, data_15_1021.2]

/-- Complete interval computation for depth 15, residue 1022. -/
theorem bounds_15_1022 : exactInterval 15 1022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1022 : oddCount 1022 15 = 11 ∧ acceleratedOrbit 15 1022 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1022) = 3 ^ 11 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1022.1, data_15_1022.2]

/-- Complete interval computation for depth 15, residue 1023. -/
theorem bounds_15_1023 : exactInterval 15 1023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1023 : oddCount 1023 15 = 11 ∧ acceleratedOrbit 15 1023 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1023) = 3 ^ 11 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1023.1, data_15_1023.2]

/-- Complete interval computation for depth 15, residue 1024. -/
theorem bounds_15_1024 : exactInterval 15 1024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1024 : oddCount 1024 15 = 3 ∧ acceleratedOrbit 15 1024 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1024) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1024.1, data_15_1024.2]

/-- Complete interval computation for depth 15, residue 1025. -/
theorem bounds_15_1025 : exactInterval 15 1025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1025 : oddCount 1025 15 = 6 ∧ acceleratedOrbit 15 1025 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1025) = 3 ^ 6 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1025.1, data_15_1025.2]

/-- Complete interval computation for depth 15, residue 1026. -/
theorem bounds_15_1026 : exactInterval 15 1026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1026 : oddCount 1026 15 = 6 ∧ acceleratedOrbit 15 1026 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1026) = 3 ^ 6 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1026.1, data_15_1026.2]

/-- Complete interval computation for depth 15, residue 1027. -/
theorem bounds_15_1027 : exactInterval 15 1027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1027 : oddCount 1027 15 = 6 ∧ acceleratedOrbit 15 1027 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1027) = 3 ^ 6 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1027.1, data_15_1027.2]

/-- Complete interval computation for depth 15, residue 1028. -/
theorem bounds_15_1028 : exactInterval 15 1028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1028 : oddCount 1028 15 = 7 ∧ acceleratedOrbit 15 1028 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1028) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1028.1, data_15_1028.2]

/-- Complete interval computation for depth 15, residue 1029. -/
theorem bounds_15_1029 : exactInterval 15 1029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1029 : oddCount 1029 15 = 7 ∧ acceleratedOrbit 15 1029 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1029) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1029.1, data_15_1029.2]

/-- Complete interval computation for depth 15, residue 1030. -/
theorem bounds_15_1030 : exactInterval 15 1030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1030 : oddCount 1030 15 = 7 ∧ acceleratedOrbit 15 1030 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1030) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1030.1, data_15_1030.2]

/-- Complete interval computation for depth 15, residue 1031. -/
theorem bounds_15_1031 : exactInterval 15 1031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1031 : oddCount 1031 15 = 6 ∧ acceleratedOrbit 15 1031 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1031) = 3 ^ 6 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1031.1, data_15_1031.2]

/-- Complete interval computation for depth 15, residue 1032. -/
theorem bounds_15_1032 : exactInterval 15 1032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1032 : oddCount 1032 15 = 7 ∧ acceleratedOrbit 15 1032 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1032) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1032.1, data_15_1032.2]

/-- Complete interval computation for depth 15, residue 1033. -/
theorem bounds_15_1033 : exactInterval 15 1033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1033 : oddCount 1033 15 = 9 ∧ acceleratedOrbit 15 1033 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1033) = 3 ^ 9 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1033.1, data_15_1033.2]

/-- Complete interval computation for depth 15, residue 1034. -/
theorem bounds_15_1034 : exactInterval 15 1034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1034 : oddCount 1034 15 = 7 ∧ acceleratedOrbit 15 1034 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1034) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1034.1, data_15_1034.2]

/-- Complete interval computation for depth 15, residue 1035. -/
theorem bounds_15_1035 : exactInterval 15 1035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1035 : oddCount 1035 15 = 7 ∧ acceleratedOrbit 15 1035 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1035) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1035.1, data_15_1035.2]

/-- Complete interval computation for depth 15, residue 1036. -/
theorem bounds_15_1036 : exactInterval 15 1036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1036 : oddCount 1036 15 = 7 ∧ acceleratedOrbit 15 1036 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1036) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1036.1, data_15_1036.2]

/-- Complete interval computation for depth 15, residue 1037. -/
theorem bounds_15_1037 : exactInterval 15 1037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1037 : oddCount 1037 15 = 7 ∧ acceleratedOrbit 15 1037 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1037) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1037.1, data_15_1037.2]

/-- Complete interval computation for depth 15, residue 1038. -/
theorem bounds_15_1038 : exactInterval 15 1038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1038 : oddCount 1038 15 = 8 ∧ acceleratedOrbit 15 1038 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1038) = 3 ^ 8 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1038.1, data_15_1038.2]

/-- Complete interval computation for depth 15, residue 1039. -/
theorem bounds_15_1039 : exactInterval 15 1039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1039 : oddCount 1039 15 = 8 ∧ acceleratedOrbit 15 1039 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1039) = 3 ^ 8 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1039.1, data_15_1039.2]

/-- Complete interval computation for depth 15, residue 1040. -/
theorem bounds_15_1040 : exactInterval 15 1040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1040 : oddCount 1040 15 = 6 ∧ acceleratedOrbit 15 1040 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1040) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1040.1, data_15_1040.2]

/-- Complete interval computation for depth 15, residue 1041. -/
theorem bounds_15_1041 : exactInterval 15 1041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1041 : oddCount 1041 15 = 7 ∧ acceleratedOrbit 15 1041 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1041) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1041.1, data_15_1041.2]

/-- Complete interval computation for depth 15, residue 1042. -/
theorem bounds_15_1042 : exactInterval 15 1042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1042 : oddCount 1042 15 = 7 ∧ acceleratedOrbit 15 1042 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1042) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1042.1, data_15_1042.2]

/-- Complete interval computation for depth 15, residue 1043. -/
theorem bounds_15_1043 : exactInterval 15 1043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1043 : oddCount 1043 15 = 7 ∧ acceleratedOrbit 15 1043 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1043) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1043.1, data_15_1043.2]

/-- Complete interval computation for depth 15, residue 1044. -/
theorem bounds_15_1044 : exactInterval 15 1044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1044 : oddCount 1044 15 = 6 ∧ acceleratedOrbit 15 1044 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1044) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1044.1, data_15_1044.2]

/-- Complete interval computation for depth 15, residue 1045. -/
theorem bounds_15_1045 : exactInterval 15 1045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1045 : oddCount 1045 15 = 6 ∧ acceleratedOrbit 15 1045 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1045) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1045.1, data_15_1045.2]

/-- Complete interval computation for depth 15, residue 1046. -/
theorem bounds_15_1046 : exactInterval 15 1046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1046 : oddCount 1046 15 = 7 ∧ acceleratedOrbit 15 1046 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1046) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1046.1, data_15_1046.2]

/-- Complete interval computation for depth 15, residue 1047. -/
theorem bounds_15_1047 : exactInterval 15 1047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1047 : oddCount 1047 15 = 7 ∧ acceleratedOrbit 15 1047 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1047) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1047.1, data_15_1047.2]

end Collatz.Research.PassageAtlas.Batch0032
