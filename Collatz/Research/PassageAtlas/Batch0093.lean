import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0093

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3014. -/
theorem bounds_15_3014 : exactInterval 15 3014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3014 : oddCount 3014 15 = 4 ∧ acceleratedOrbit 15 3014 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3014) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3014.1, data_15_3014.2]

/-- Complete interval computation for depth 15, residue 3015. -/
theorem bounds_15_3015 : exactInterval 15 3015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3015 : oddCount 3015 15 = 10 ∧ acceleratedOrbit 15 3015 = 5437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3015) = 3 ^ 10 * m + 5437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3015.1, data_15_3015.2]

/-- Complete interval computation for depth 15, residue 3016. -/
theorem bounds_15_3016 : exactInterval 15 3016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3016 : oddCount 3016 15 = 9 ∧ acceleratedOrbit 15 3016 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3016) = 3 ^ 9 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3016.1, data_15_3016.2]

/-- Complete interval computation for depth 15, residue 3017. -/
theorem bounds_15_3017 : exactInterval 15 3017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3017 : oddCount 3017 15 = 8 ∧ acceleratedOrbit 15 3017 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3017) = 3 ^ 8 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3017.1, data_15_3017.2]

/-- Complete interval computation for depth 15, residue 3018. -/
theorem bounds_15_3018 : exactInterval 15 3018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3018 : oddCount 3018 15 = 9 ∧ acceleratedOrbit 15 3018 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3018) = 3 ^ 9 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3018.1, data_15_3018.2]

/-- Complete interval computation for depth 15, residue 3019. -/
theorem bounds_15_3019 : exactInterval 15 3019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3019 : oddCount 3019 15 = 8 ∧ acceleratedOrbit 15 3019 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3019) = 3 ^ 8 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3019.1, data_15_3019.2]

/-- Complete interval computation for depth 15, residue 3020. -/
theorem bounds_15_3020 : exactInterval 15 3020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3020 : oddCount 3020 15 = 9 ∧ acceleratedOrbit 15 3020 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3020) = 3 ^ 9 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3020.1, data_15_3020.2]

/-- Complete interval computation for depth 15, residue 3021. -/
theorem bounds_15_3021 : exactInterval 15 3021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3021 : oddCount 3021 15 = 9 ∧ acceleratedOrbit 15 3021 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3021) = 3 ^ 9 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3021.1, data_15_3021.2]

/-- Complete interval computation for depth 15, residue 3022. -/
theorem bounds_15_3022 : exactInterval 15 3022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3022 : oddCount 3022 15 = 10 ∧ acceleratedOrbit 15 3022 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3022) = 3 ^ 10 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3022.1, data_15_3022.2]

/-- Complete interval computation for depth 15, residue 3023. -/
theorem bounds_15_3023 : exactInterval 15 3023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3023 : oddCount 3023 15 = 10 ∧ acceleratedOrbit 15 3023 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3023) = 3 ^ 10 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3023.1, data_15_3023.2]

/-- Complete interval computation for depth 15, residue 3024. -/
theorem bounds_15_3024 : exactInterval 15 3024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3024 : oddCount 3024 15 = 7 ∧ acceleratedOrbit 15 3024 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3024) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3024.1, data_15_3024.2]

/-- Complete interval computation for depth 15, residue 3025. -/
theorem bounds_15_3025 : exactInterval 15 3025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3025 : oddCount 3025 15 = 9 ∧ acceleratedOrbit 15 3025 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3025) = 3 ^ 9 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3025.1, data_15_3025.2]

/-- Complete interval computation for depth 15, residue 3026. -/
theorem bounds_15_3026 : exactInterval 15 3026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3026 : oddCount 3026 15 = 9 ∧ acceleratedOrbit 15 3026 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3026) = 3 ^ 9 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3026.1, data_15_3026.2]

/-- Complete interval computation for depth 15, residue 3027. -/
theorem bounds_15_3027 : exactInterval 15 3027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3027 : oddCount 3027 15 = 9 ∧ acceleratedOrbit 15 3027 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3027) = 3 ^ 9 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3027.1, data_15_3027.2]

/-- Complete interval computation for depth 15, residue 3028. -/
theorem bounds_15_3028 : exactInterval 15 3028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3028 : oddCount 3028 15 = 7 ∧ acceleratedOrbit 15 3028 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3028) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3028.1, data_15_3028.2]

/-- Complete interval computation for depth 15, residue 3029. -/
theorem bounds_15_3029 : exactInterval 15 3029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3029 : oddCount 3029 15 = 7 ∧ acceleratedOrbit 15 3029 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3029) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3029.1, data_15_3029.2]

/-- Complete interval computation for depth 15, residue 3030. -/
theorem bounds_15_3030 : exactInterval 15 3030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3030 : oddCount 3030 15 = 11 ∧ acceleratedOrbit 15 3030 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3030) = 3 ^ 11 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3030.1, data_15_3030.2]

/-- Complete interval computation for depth 15, residue 3031. -/
theorem bounds_15_3031 : exactInterval 15 3031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3031 : oddCount 3031 15 = 11 ∧ acceleratedOrbit 15 3031 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3031) = 3 ^ 11 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3031.1, data_15_3031.2]

/-- Complete interval computation for depth 15, residue 3032. -/
theorem bounds_15_3032 : exactInterval 15 3032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3032 : oddCount 3032 15 = 8 ∧ acceleratedOrbit 15 3032 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3032) = 3 ^ 8 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3032.1, data_15_3032.2]

/-- Complete interval computation for depth 15, residue 3033. -/
theorem bounds_15_3033 : exactInterval 15 3033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3033 : oddCount 3033 15 = 4 ∧ acceleratedOrbit 15 3033 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3033) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3033.1, data_15_3033.2]

/-- Complete interval computation for depth 15, residue 3034. -/
theorem bounds_15_3034 : exactInterval 15 3034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3034 : oddCount 3034 15 = 8 ∧ acceleratedOrbit 15 3034 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3034) = 3 ^ 8 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3034.1, data_15_3034.2]

/-- Complete interval computation for depth 15, residue 3035. -/
theorem bounds_15_3035 : exactInterval 15 3035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3035 : oddCount 3035 15 = 9 ∧ acceleratedOrbit 15 3035 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3035) = 3 ^ 9 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3035.1, data_15_3035.2]

/-- Complete interval computation for depth 15, residue 3036. -/
theorem bounds_15_3036 : exactInterval 15 3036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3036 : oddCount 3036 15 = 8 ∧ acceleratedOrbit 15 3036 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3036) = 3 ^ 8 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3036.1, data_15_3036.2]

/-- Complete interval computation for depth 15, residue 3037. -/
theorem bounds_15_3037 : exactInterval 15 3037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3037 : oddCount 3037 15 = 8 ∧ acceleratedOrbit 15 3037 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3037) = 3 ^ 8 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3037.1, data_15_3037.2]

/-- Complete interval computation for depth 15, residue 3038. -/
theorem bounds_15_3038 : exactInterval 15 3038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3038 : oddCount 3038 15 = 10 ∧ acceleratedOrbit 15 3038 = 5480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3038) = 3 ^ 10 * m + 5480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3038.1, data_15_3038.2]

/-- Complete interval computation for depth 15, residue 3039. -/
theorem bounds_15_3039 : exactInterval 15 3039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3039 : oddCount 3039 15 = 10 ∧ acceleratedOrbit 15 3039 = 5480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3039) = 3 ^ 10 * m + 5480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3039.1, data_15_3039.2]

/-- Complete interval computation for depth 15, residue 3040. -/
theorem bounds_15_3040 : exactInterval 15 3040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3040 : oddCount 3040 15 = 7 ∧ acceleratedOrbit 15 3040 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3040) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3040.1, data_15_3040.2]

/-- Complete interval computation for depth 15, residue 3041. -/
theorem bounds_15_3041 : exactInterval 15 3041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3041 : oddCount 3041 15 = 9 ∧ acceleratedOrbit 15 3041 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3041) = 3 ^ 9 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3041.1, data_15_3041.2]

/-- Complete interval computation for depth 15, residue 3042. -/
theorem bounds_15_3042 : exactInterval 15 3042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3042 : oddCount 3042 15 = 7 ∧ acceleratedOrbit 15 3042 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3042) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3042.1, data_15_3042.2]

/-- Complete interval computation for depth 15, residue 3043. -/
theorem bounds_15_3043 : exactInterval 15 3043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3043 : oddCount 3043 15 = 7 ∧ acceleratedOrbit 15 3043 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3043) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3043.1, data_15_3043.2]

/-- Complete interval computation for depth 15, residue 3044. -/
theorem bounds_15_3044 : exactInterval 15 3044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3044 : oddCount 3044 15 = 6 ∧ acceleratedOrbit 15 3044 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3044) = 3 ^ 6 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3044.1, data_15_3044.2]

/-- Complete interval computation for depth 15, residue 3045. -/
theorem bounds_15_3045 : exactInterval 15 3045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3045 : oddCount 3045 15 = 6 ∧ acceleratedOrbit 15 3045 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3045) = 3 ^ 6 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3045.1, data_15_3045.2]

/-- Complete interval computation for depth 15, residue 3046. -/
theorem bounds_15_3046 : exactInterval 15 3046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3046 : oddCount 3046 15 = 6 ∧ acceleratedOrbit 15 3046 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3046) = 3 ^ 6 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3046.1, data_15_3046.2]

end Collatz.Research.PassageAtlas.Batch0093
