import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0664

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3015. -/
theorem bounds_13_3015 : exactInterval 13 3015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3015 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3015) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3015 : oddCount 3015 13 = 9 ∧ acceleratedOrbit 13 3015 = 7249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3015 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3015) = 3 ^ 9 * m + 7249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3015.1, data_13_3015.2]

/-- Complete interval computation for depth 13, residue 3016. -/
theorem bounds_13_3016 : exactInterval 13 3016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3016 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3016) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3016 : oddCount 3016 13 = 8 ∧ acceleratedOrbit 13 3016 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3016 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3016) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3016.1, data_13_3016.2]

/-- Complete interval computation for depth 13, residue 3017. -/
theorem bounds_13_3017 : exactInterval 13 3017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3017 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3017) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3017 : oddCount 3017 13 = 8 ∧ acceleratedOrbit 13 3017 = 2420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3017 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3017) = 3 ^ 8 * m + 2420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3017.1, data_13_3017.2]

/-- Complete interval computation for depth 13, residue 3018. -/
theorem bounds_13_3018 : exactInterval 13 3018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3018 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3018) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3018 : oddCount 3018 13 = 8 ∧ acceleratedOrbit 13 3018 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3018 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3018) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3018.1, data_13_3018.2]

/-- Complete interval computation for depth 13, residue 3019. -/
theorem bounds_13_3019 : exactInterval 13 3019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3019 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3019) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3019 : oddCount 3019 13 = 7 ∧ acceleratedOrbit 13 3019 = 809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3019 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3019) = 3 ^ 7 * m + 809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3019.1, data_13_3019.2]

/-- Complete interval computation for depth 13, residue 3020. -/
theorem bounds_13_3020 : exactInterval 13 3020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3020 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3020) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3020 : oddCount 3020 13 = 8 ∧ acceleratedOrbit 13 3020 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3020 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3020) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3020.1, data_13_3020.2]

/-- Complete interval computation for depth 13, residue 3021. -/
theorem bounds_13_3021 : exactInterval 13 3021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3021 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3021) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3021 : oddCount 3021 13 = 8 ∧ acceleratedOrbit 13 3021 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3021 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3021) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3021.1, data_13_3021.2]

/-- Complete interval computation for depth 13, residue 3022. -/
theorem bounds_13_3022 : exactInterval 13 3022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3022 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3022) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3022 : oddCount 3022 13 = 8 ∧ acceleratedOrbit 13 3022 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3022 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3022) = 3 ^ 8 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3022.1, data_13_3022.2]

/-- Complete interval computation for depth 13, residue 3023. -/
theorem bounds_13_3023 : exactInterval 13 3023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3023 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3023) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3023 : oddCount 3023 13 = 8 ∧ acceleratedOrbit 13 3023 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3023 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3023) = 3 ^ 8 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3023.1, data_13_3023.2]

/-- Complete interval computation for depth 13, residue 3024. -/
theorem bounds_13_3024 : exactInterval 13 3024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3024 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3024) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3024 : oddCount 3024 13 = 5 ∧ acceleratedOrbit 13 3024 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3024 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3024) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3024.1, data_13_3024.2]

/-- Complete interval computation for depth 13, residue 3025. -/
theorem bounds_13_3025 : exactInterval 13 3025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3025 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3025) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3025 : oddCount 3025 13 = 8 ∧ acceleratedOrbit 13 3025 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3025 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3025) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3025.1, data_13_3025.2]

/-- Complete interval computation for depth 13, residue 3026. -/
theorem bounds_13_3026 : exactInterval 13 3026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3026 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3026) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3026 : oddCount 3026 13 = 9 ∧ acceleratedOrbit 13 3026 = 7280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3026 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3026) = 3 ^ 9 * m + 7280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3026.1, data_13_3026.2]

/-- Complete interval computation for depth 13, residue 3027. -/
theorem bounds_13_3027 : exactInterval 13 3027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3027 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3027) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3027 : oddCount 3027 13 = 9 ∧ acceleratedOrbit 13 3027 = 7280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3027 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3027) = 3 ^ 9 * m + 7280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3027.1, data_13_3027.2]

/-- Complete interval computation for depth 13, residue 3028. -/
theorem bounds_13_3028 : exactInterval 13 3028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3028 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3028) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3028 : oddCount 3028 13 = 5 ∧ acceleratedOrbit 13 3028 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3028 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3028) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3028.1, data_13_3028.2]

/-- Complete interval computation for depth 13, residue 3029. -/
theorem bounds_13_3029 : exactInterval 13 3029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3029 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3029) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3029 : oddCount 3029 13 = 5 ∧ acceleratedOrbit 13 3029 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3029 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3029) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3029.1, data_13_3029.2]

/-- Complete interval computation for depth 13, residue 3030. -/
theorem bounds_13_3030 : exactInterval 13 3030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3030 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3030) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3030 : oddCount 3030 13 = 10 ∧ acceleratedOrbit 13 3030 = 21869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3030 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3030) = 3 ^ 10 * m + 21869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3030.1, data_13_3030.2]

end Collatz.Research.StoppingAtlas.Batch0664
