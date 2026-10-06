import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0267

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1013. -/
theorem bounds_12_1013 : exactInterval 12 1013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1013 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1013) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1013 : oddCount 1013 12 = 6 ∧ acceleratedOrbit 12 1013 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1013 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1013) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1013.1, data_12_1013.2]

/-- Complete interval computation for depth 12, residue 1014. -/
theorem bounds_12_1014 : exactInterval 12 1014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1014 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1014) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1014 : oddCount 1014 12 = 6 ∧ acceleratedOrbit 12 1014 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1014 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1014) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1014.1, data_12_1014.2]

/-- Complete interval computation for depth 12, residue 1015. -/
theorem bounds_12_1015 : exactInterval 12 1015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1015 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1015) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1015 : oddCount 1015 12 = 6 ∧ acceleratedOrbit 12 1015 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1015 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1015) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1015.1, data_12_1015.2]

/-- Complete interval computation for depth 12, residue 1016. -/
theorem bounds_12_1016 : exactInterval 12 1016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1016 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1016) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1016 : oddCount 1016 12 = 8 ∧ acceleratedOrbit 12 1016 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1016 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1016) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1016.1, data_12_1016.2]

/-- Complete interval computation for depth 12, residue 1017. -/
theorem bounds_12_1017 : exactInterval 12 1017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1017 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1017) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1017 : oddCount 1017 12 = 8 ∧ acceleratedOrbit 12 1017 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1017 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1017) = 3 ^ 8 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1017.1, data_12_1017.2]

/-- Complete interval computation for depth 12, residue 1018. -/
theorem bounds_12_1018 : exactInterval 12 1018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1018 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1018) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1018 : oddCount 1018 12 = 8 ∧ acceleratedOrbit 12 1018 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1018 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1018) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1018.1, data_12_1018.2]

/-- Complete interval computation for depth 12, residue 1019. -/
theorem bounds_12_1019 : exactInterval 12 1019 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1019 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1019) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1019 : oddCount 1019 12 = 7 ∧ acceleratedOrbit 12 1019 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1019 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1019) = 3 ^ 7 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1019.1, data_12_1019.2]

/-- Complete interval computation for depth 12, residue 1020. -/
theorem bounds_12_1020 : exactInterval 12 1020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1020 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1020) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1020 : oddCount 1020 12 = 8 ∧ acceleratedOrbit 12 1020 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1020 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1020) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1020.1, data_12_1020.2]

/-- Complete interval computation for depth 12, residue 1021. -/
theorem bounds_12_1021 : exactInterval 12 1021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1021 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1021) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1021 : oddCount 1021 12 = 8 ∧ acceleratedOrbit 12 1021 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1021 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1021) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1021.1, data_12_1021.2]

/-- Complete interval computation for depth 12, residue 1022. -/
theorem bounds_12_1022 : exactInterval 12 1022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1022 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1022) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1022 : oddCount 1022 12 = 10 ∧ acceleratedOrbit 12 1022 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1022 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1022) = 3 ^ 10 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1022.1, data_12_1022.2]

/-- Complete interval computation for depth 12, residue 1023. -/
theorem bounds_12_1023 : exactInterval 12 1023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1023 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1023) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1023 : oddCount 1023 12 = 10 ∧ acceleratedOrbit 12 1023 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1023 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1023) = 3 ^ 10 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1023.1, data_12_1023.2]

/-- Complete interval computation for depth 12, residue 1024. -/
theorem bounds_12_1024 : exactInterval 12 1024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1024 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1024) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1024 : oddCount 1024 12 = 1 ∧ acceleratedOrbit 12 1024 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1024 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1024) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1024.1, data_12_1024.2]

/-- Complete interval computation for depth 12, residue 1025. -/
theorem bounds_12_1025 : exactInterval 12 1025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1025 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1025) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1025 : oddCount 1025 12 = 5 ∧ acceleratedOrbit 12 1025 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1025 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1025) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1025.1, data_12_1025.2]

/-- Complete interval computation for depth 12, residue 1026. -/
theorem bounds_12_1026 : exactInterval 12 1026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1026 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1026) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1026 : oddCount 1026 12 = 6 ∧ acceleratedOrbit 12 1026 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1026 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1026) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1026.1, data_12_1026.2]

/-- Complete interval computation for depth 12, residue 1027. -/
theorem bounds_12_1027 : exactInterval 12 1027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1027 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1027) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1027 : oddCount 1027 12 = 6 ∧ acceleratedOrbit 12 1027 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1027 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1027) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1027.1, data_12_1027.2]

/-- Complete interval computation for depth 12, residue 1028. -/
theorem bounds_12_1028 : exactInterval 12 1028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1028 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1028) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1028 : oddCount 1028 12 = 5 ∧ acceleratedOrbit 12 1028 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1028 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1028) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1028.1, data_12_1028.2]

end Collatz.Research.StoppingAtlas.Batch0267
