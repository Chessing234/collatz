import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0795

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26017. -/
theorem bounds_15_26017 : exactInterval 15 26017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26017 : oddCount 26017 15 = 9 ∧ acceleratedOrbit 15 26017 = 15632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26017) = 3 ^ 9 * m + 15632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26017.1, data_15_26017.2]

/-- Complete interval computation for depth 15, residue 26018. -/
theorem bounds_15_26018 : exactInterval 15 26018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26018 : oddCount 26018 15 = 5 ∧ acceleratedOrbit 15 26018 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26018) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26018.1, data_15_26018.2]

/-- Complete interval computation for depth 15, residue 26019. -/
theorem bounds_15_26019 : exactInterval 15 26019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26019 : oddCount 26019 15 = 5 ∧ acceleratedOrbit 15 26019 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26019) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26019.1, data_15_26019.2]

/-- Complete interval computation for depth 15, residue 26020. -/
theorem bounds_15_26020 : exactInterval 15 26020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26020 : oddCount 26020 15 = 5 ∧ acceleratedOrbit 15 26020 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26020) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26020.1, data_15_26020.2]

/-- Complete interval computation for depth 15, residue 26021. -/
theorem bounds_15_26021 : exactInterval 15 26021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26021 : oddCount 26021 15 = 5 ∧ acceleratedOrbit 15 26021 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26021) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26021.1, data_15_26021.2]

/-- Complete interval computation for depth 15, residue 26022. -/
theorem bounds_15_26022 : exactInterval 15 26022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26022 : oddCount 26022 15 = 5 ∧ acceleratedOrbit 15 26022 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26022) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26022.1, data_15_26022.2]

/-- Complete interval computation for depth 15, residue 26023. -/
theorem bounds_15_26023 : exactInterval 15 26023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26023 : oddCount 26023 15 = 11 ∧ acceleratedOrbit 15 26023 = 140696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26023) = 3 ^ 11 * m + 140696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26023.1, data_15_26023.2]

/-- Complete interval computation for depth 15, residue 26024. -/
theorem bounds_15_26024 : exactInterval 15 26024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26024 : oddCount 26024 15 = 4 ∧ acceleratedOrbit 15 26024 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26024) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26024.1, data_15_26024.2]

/-- Complete interval computation for depth 15, residue 26025. -/
theorem bounds_15_26025 : exactInterval 15 26025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26025 : oddCount 26025 15 = 9 ∧ acceleratedOrbit 15 26025 = 15634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26025) = 3 ^ 9 * m + 15634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26025.1, data_15_26025.2]

/-- Complete interval computation for depth 15, residue 26026. -/
theorem bounds_15_26026 : exactInterval 15 26026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26026 : oddCount 26026 15 = 4 ∧ acceleratedOrbit 15 26026 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26026) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26026.1, data_15_26026.2]

/-- Complete interval computation for depth 15, residue 26027. -/
theorem bounds_15_26027 : exactInterval 15 26027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26027 : oddCount 26027 15 = 8 ∧ acceleratedOrbit 15 26027 = 5212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26027) = 3 ^ 8 * m + 5212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26027.1, data_15_26027.2]

/-- Complete interval computation for depth 15, residue 26028. -/
theorem bounds_15_26028 : exactInterval 15 26028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26028 : oddCount 26028 15 = 7 ∧ acceleratedOrbit 15 26028 = 1738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26028) = 3 ^ 7 * m + 1738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26028.1, data_15_26028.2]

/-- Complete interval computation for depth 15, residue 26029. -/
theorem bounds_15_26029 : exactInterval 15 26029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26029 : oddCount 26029 15 = 7 ∧ acceleratedOrbit 15 26029 = 1738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26029) = 3 ^ 7 * m + 1738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26029.1, data_15_26029.2]

/-- Complete interval computation for depth 15, residue 26030. -/
theorem bounds_15_26030 : exactInterval 15 26030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26030 : oddCount 26030 15 = 7 ∧ acceleratedOrbit 15 26030 = 1738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26030) = 3 ^ 7 * m + 1738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26030.1, data_15_26030.2]

/-- Complete interval computation for depth 15, residue 26031. -/
theorem bounds_15_26031 : exactInterval 15 26031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26031 : oddCount 26031 15 = 8 ∧ acceleratedOrbit 15 26031 = 5213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26031) = 3 ^ 8 * m + 5213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26031.1, data_15_26031.2]

/-- Complete interval computation for depth 15, residue 26032. -/
theorem bounds_15_26032 : exactInterval 15 26032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26032 : oddCount 26032 15 = 7 ∧ acceleratedOrbit 15 26032 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26032) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26032.1, data_15_26032.2]

/-- Complete interval computation for depth 15, residue 26033. -/
theorem bounds_15_26033 : exactInterval 15 26033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26033 : oddCount 26033 15 = 6 ∧ acceleratedOrbit 15 26033 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26033) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26033.1, data_15_26033.2]

/-- Complete interval computation for depth 15, residue 26034. -/
theorem bounds_15_26034 : exactInterval 15 26034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26034 : oddCount 26034 15 = 6 ∧ acceleratedOrbit 15 26034 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26034) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26034.1, data_15_26034.2]

/-- Complete interval computation for depth 15, residue 26035. -/
theorem bounds_15_26035 : exactInterval 15 26035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26035 : oddCount 26035 15 = 6 ∧ acceleratedOrbit 15 26035 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26035) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26035.1, data_15_26035.2]

/-- Complete interval computation for depth 15, residue 26036. -/
theorem bounds_15_26036 : exactInterval 15 26036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26036 : oddCount 26036 15 = 7 ∧ acceleratedOrbit 15 26036 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26036) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26036.1, data_15_26036.2]

/-- Complete interval computation for depth 15, residue 26037. -/
theorem bounds_15_26037 : exactInterval 15 26037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26037 : oddCount 26037 15 = 7 ∧ acceleratedOrbit 15 26037 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26037) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26037.1, data_15_26037.2]

/-- Complete interval computation for depth 15, residue 26038. -/
theorem bounds_15_26038 : exactInterval 15 26038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26038 : oddCount 26038 15 = 9 ∧ acceleratedOrbit 15 26038 = 15643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26038) = 3 ^ 9 * m + 15643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26038.1, data_15_26038.2]

/-- Complete interval computation for depth 15, residue 26039. -/
theorem bounds_15_26039 : exactInterval 15 26039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26039 : oddCount 26039 15 = 9 ∧ acceleratedOrbit 15 26039 = 15643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26039) = 3 ^ 9 * m + 15643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26039.1, data_15_26039.2]

/-- Complete interval computation for depth 15, residue 26040. -/
theorem bounds_15_26040 : exactInterval 15 26040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26040 : oddCount 26040 15 = 7 ∧ acceleratedOrbit 15 26040 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26040) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26040.1, data_15_26040.2]

/-- Complete interval computation for depth 15, residue 26041. -/
theorem bounds_15_26041 : exactInterval 15 26041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26041 : oddCount 26041 15 = 6 ∧ acceleratedOrbit 15 26041 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26041) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26041.1, data_15_26041.2]

/-- Complete interval computation for depth 15, residue 26042. -/
theorem bounds_15_26042 : exactInterval 15 26042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26042 : oddCount 26042 15 = 7 ∧ acceleratedOrbit 15 26042 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26042) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26042.1, data_15_26042.2]

/-- Complete interval computation for depth 15, residue 26043. -/
theorem bounds_15_26043 : exactInterval 15 26043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26043 : oddCount 26043 15 = 9 ∧ acceleratedOrbit 15 26043 = 15646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26043) = 3 ^ 9 * m + 15646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26043.1, data_15_26043.2]

/-- Complete interval computation for depth 15, residue 26044. -/
theorem bounds_15_26044 : exactInterval 15 26044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26044 : oddCount 26044 15 = 7 ∧ acceleratedOrbit 15 26044 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26044) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26044.1, data_15_26044.2]

/-- Complete interval computation for depth 15, residue 26045. -/
theorem bounds_15_26045 : exactInterval 15 26045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26045 : oddCount 26045 15 = 7 ∧ acceleratedOrbit 15 26045 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26045) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26045.1, data_15_26045.2]

/-- Complete interval computation for depth 15, residue 26046. -/
theorem bounds_15_26046 : exactInterval 15 26046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26046 : oddCount 26046 15 = 7 ∧ acceleratedOrbit 15 26046 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26046) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26046.1, data_15_26046.2]

/-- Complete interval computation for depth 15, residue 26047. -/
theorem bounds_15_26047 : exactInterval 15 26047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26047 : oddCount 26047 15 = 13 ∧ acceleratedOrbit 15 26047 = 1267366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26047) = 3 ^ 13 * m + 1267366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26047.1, data_15_26047.2]

/-- Complete interval computation for depth 15, residue 26048. -/
theorem bounds_15_26048 : exactInterval 15 26048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26048 : oddCount 26048 15 = 4 ∧ acceleratedOrbit 15 26048 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26048) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26048.1, data_15_26048.2]

/-- Complete interval computation for depth 15, residue 26049. -/
theorem bounds_15_26049 : exactInterval 15 26049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26049 : oddCount 26049 15 = 7 ∧ acceleratedOrbit 15 26049 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26049) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26049.1, data_15_26049.2]

end Collatz.Research.PassageAtlas.Batch0795
