import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0729

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4014. -/
theorem bounds_13_4014 : exactInterval 13 4014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4014 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4014) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4014 : oddCount 4014 13 = 7 ∧ acceleratedOrbit 13 4014 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4014 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4014) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4014.1, data_13_4014.2]

/-- Complete interval computation for depth 13, residue 4015. -/
theorem bounds_13_4015 : exactInterval 13 4015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4015 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4015) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4015 : oddCount 4015 13 = 7 ∧ acceleratedOrbit 13 4015 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4015 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4015) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4015.1, data_13_4015.2]

/-- Complete interval computation for depth 13, residue 4016. -/
theorem bounds_13_4016 : exactInterval 13 4016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4016 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4016) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4016 : oddCount 4016 13 = 7 ∧ acceleratedOrbit 13 4016 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4016 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4016) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4016.1, data_13_4016.2]

/-- Complete interval computation for depth 13, residue 4017. -/
theorem bounds_13_4017 : exactInterval 13 4017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4017 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4017) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4017 : oddCount 4017 13 = 4 ∧ acceleratedOrbit 13 4017 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4017 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4017) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4017.1, data_13_4017.2]

/-- Complete interval computation for depth 13, residue 4018. -/
theorem bounds_13_4018 : exactInterval 13 4018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4018 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4018) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4018 : oddCount 4018 13 = 4 ∧ acceleratedOrbit 13 4018 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4018 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4018) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4018.1, data_13_4018.2]

/-- Complete interval computation for depth 13, residue 4019. -/
theorem bounds_13_4019 : exactInterval 13 4019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4019 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4019) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4019 : oddCount 4019 13 = 4 ∧ acceleratedOrbit 13 4019 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4019 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4019) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4019.1, data_13_4019.2]

/-- Complete interval computation for depth 13, residue 4020. -/
theorem bounds_13_4020 : exactInterval 13 4020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4020 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4020) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4020 : oddCount 4020 13 = 7 ∧ acceleratedOrbit 13 4020 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4020 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4020) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4020.1, data_13_4020.2]

/-- Complete interval computation for depth 13, residue 4021. -/
theorem bounds_13_4021 : exactInterval 13 4021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4021 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4021) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4021 : oddCount 4021 13 = 7 ∧ acceleratedOrbit 13 4021 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4021 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4021) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4021.1, data_13_4021.2]

/-- Complete interval computation for depth 13, residue 4022. -/
theorem bounds_13_4022 : exactInterval 13 4022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4022 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4022) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4022 : oddCount 4022 13 = 7 ∧ acceleratedOrbit 13 4022 = 1075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4022 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4022) = 3 ^ 7 * m + 1075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4022.1, data_13_4022.2]

/-- Complete interval computation for depth 13, residue 4023. -/
theorem bounds_13_4023 : exactInterval 13 4023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4023 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4023) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4023 : oddCount 4023 13 = 7 ∧ acceleratedOrbit 13 4023 = 1075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4023 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4023) = 3 ^ 7 * m + 1075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4023.1, data_13_4023.2]

/-- Complete interval computation for depth 13, residue 4024. -/
theorem bounds_13_4024 : exactInterval 13 4024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4024 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4024) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4024 : oddCount 4024 13 = 7 ∧ acceleratedOrbit 13 4024 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4024 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4024) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4024.1, data_13_4024.2]

/-- Complete interval computation for depth 13, residue 4025. -/
theorem bounds_13_4025 : exactInterval 13 4025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4025 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4025) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4025 : oddCount 4025 13 = 6 ∧ acceleratedOrbit 13 4025 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4025 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4025) = 3 ^ 6 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4025.1, data_13_4025.2]

/-- Complete interval computation for depth 13, residue 4026. -/
theorem bounds_13_4026 : exactInterval 13 4026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4026 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4026) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4026 : oddCount 4026 13 = 7 ∧ acceleratedOrbit 13 4026 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4026 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4026) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4026.1, data_13_4026.2]

/-- Complete interval computation for depth 13, residue 4027. -/
theorem bounds_13_4027 : exactInterval 13 4027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4027 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4027) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4027 : oddCount 4027 13 = 6 ∧ acceleratedOrbit 13 4027 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4027 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4027) = 3 ^ 6 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4027.1, data_13_4027.2]

/-- Complete interval computation for depth 13, residue 4028. -/
theorem bounds_13_4028 : exactInterval 13 4028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4028 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4028) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4028 : oddCount 4028 13 = 8 ∧ acceleratedOrbit 13 4028 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4028 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4028) = 3 ^ 8 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4028.1, data_13_4028.2]

end Collatz.Research.StoppingAtlas.Batch0729
