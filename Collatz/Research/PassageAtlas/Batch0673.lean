import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0673

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22020. -/
theorem bounds_15_22020 : exactInterval 15 22020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22020 : oddCount 22020 15 = 7 ∧ acceleratedOrbit 15 22020 = 1471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22020) = 3 ^ 7 * m + 1471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22020.1, data_15_22020.2]

/-- Complete interval computation for depth 15, residue 22021. -/
theorem bounds_15_22021 : exactInterval 15 22021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22021 : oddCount 22021 15 = 7 ∧ acceleratedOrbit 15 22021 = 1471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22021) = 3 ^ 7 * m + 1471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22021.1, data_15_22021.2]

/-- Complete interval computation for depth 15, residue 22022. -/
theorem bounds_15_22022 : exactInterval 15 22022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22022 : oddCount 22022 15 = 7 ∧ acceleratedOrbit 15 22022 = 1471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22022) = 3 ^ 7 * m + 1471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22022.1, data_15_22022.2]

/-- Complete interval computation for depth 15, residue 22023. -/
theorem bounds_15_22023 : exactInterval 15 22023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22023 : oddCount 22023 15 = 6 ∧ acceleratedOrbit 15 22023 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22023) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22023.1, data_15_22023.2]

/-- Complete interval computation for depth 15, residue 22024. -/
theorem bounds_15_22024 : exactInterval 15 22024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22024 : oddCount 22024 15 = 5 ∧ acceleratedOrbit 15 22024 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22024) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22024.1, data_15_22024.2]

/-- Complete interval computation for depth 15, residue 22025. -/
theorem bounds_15_22025 : exactInterval 15 22025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22025 : oddCount 22025 15 = 8 ∧ acceleratedOrbit 15 22025 = 4411 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22025) = 3 ^ 8 * m + 4411 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22025.1, data_15_22025.2]

/-- Complete interval computation for depth 15, residue 22026. -/
theorem bounds_15_22026 : exactInterval 15 22026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22026 : oddCount 22026 15 = 5 ∧ acceleratedOrbit 15 22026 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22026) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22026.1, data_15_22026.2]

/-- Complete interval computation for depth 15, residue 22027. -/
theorem bounds_15_22027 : exactInterval 15 22027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22027 : oddCount 22027 15 = 7 ∧ acceleratedOrbit 15 22027 = 1471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22027) = 3 ^ 7 * m + 1471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22027.1, data_15_22027.2]

/-- Complete interval computation for depth 15, residue 22028. -/
theorem bounds_15_22028 : exactInterval 15 22028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22028 : oddCount 22028 15 = 5 ∧ acceleratedOrbit 15 22028 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22028) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22028.1, data_15_22028.2]

/-- Complete interval computation for depth 15, residue 22029. -/
theorem bounds_15_22029 : exactInterval 15 22029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22029 : oddCount 22029 15 = 5 ∧ acceleratedOrbit 15 22029 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22029) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22029.1, data_15_22029.2]

/-- Complete interval computation for depth 15, residue 22030. -/
theorem bounds_15_22030 : exactInterval 15 22030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22030 : oddCount 22030 15 = 8 ∧ acceleratedOrbit 15 22030 = 4412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22030) = 3 ^ 8 * m + 4412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22030.1, data_15_22030.2]

/-- Complete interval computation for depth 15, residue 22031. -/
theorem bounds_15_22031 : exactInterval 15 22031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22031 : oddCount 22031 15 = 8 ∧ acceleratedOrbit 15 22031 = 4412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22031) = 3 ^ 8 * m + 4412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22031.1, data_15_22031.2]

/-- Complete interval computation for depth 15, residue 22032. -/
theorem bounds_15_22032 : exactInterval 15 22032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22032 : oddCount 22032 15 = 6 ∧ acceleratedOrbit 15 22032 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22032) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22032.1, data_15_22032.2]

/-- Complete interval computation for depth 15, residue 22033. -/
theorem bounds_15_22033 : exactInterval 15 22033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22033 : oddCount 22033 15 = 5 ∧ acceleratedOrbit 15 22033 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22033) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22033.1, data_15_22033.2]

/-- Complete interval computation for depth 15, residue 22034. -/
theorem bounds_15_22034 : exactInterval 15 22034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22034 : oddCount 22034 15 = 10 ∧ acceleratedOrbit 15 22034 = 39716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22034) = 3 ^ 10 * m + 39716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22034.1, data_15_22034.2]

/-- Complete interval computation for depth 15, residue 22035. -/
theorem bounds_15_22035 : exactInterval 15 22035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22035 : oddCount 22035 15 = 10 ∧ acceleratedOrbit 15 22035 = 39716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22035) = 3 ^ 10 * m + 39716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22035.1, data_15_22035.2]

/-- Complete interval computation for depth 15, residue 22036. -/
theorem bounds_15_22036 : exactInterval 15 22036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22036 : oddCount 22036 15 = 6 ∧ acceleratedOrbit 15 22036 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22036) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22036.1, data_15_22036.2]

/-- Complete interval computation for depth 15, residue 22037. -/
theorem bounds_15_22037 : exactInterval 15 22037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22037 : oddCount 22037 15 = 6 ∧ acceleratedOrbit 15 22037 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22037) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22037.1, data_15_22037.2]

/-- Complete interval computation for depth 15, residue 22038. -/
theorem bounds_15_22038 : exactInterval 15 22038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22038 : oddCount 22038 15 = 9 ∧ acceleratedOrbit 15 22038 = 13243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22038) = 3 ^ 9 * m + 13243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22038.1, data_15_22038.2]

/-- Complete interval computation for depth 15, residue 22039. -/
theorem bounds_15_22039 : exactInterval 15 22039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22039 : oddCount 22039 15 = 9 ∧ acceleratedOrbit 15 22039 = 13243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22039) = 3 ^ 9 * m + 13243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22039.1, data_15_22039.2]

/-- Complete interval computation for depth 15, residue 22040. -/
theorem bounds_15_22040 : exactInterval 15 22040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22040 : oddCount 22040 15 = 6 ∧ acceleratedOrbit 15 22040 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22040) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22040.1, data_15_22040.2]

/-- Complete interval computation for depth 15, residue 22041. -/
theorem bounds_15_22041 : exactInterval 15 22041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22041 : oddCount 22041 15 = 9 ∧ acceleratedOrbit 15 22041 = 13243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22041) = 3 ^ 9 * m + 13243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22041.1, data_15_22041.2]

/-- Complete interval computation for depth 15, residue 22042. -/
theorem bounds_15_22042 : exactInterval 15 22042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22042 : oddCount 22042 15 = 6 ∧ acceleratedOrbit 15 22042 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22042) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22042.1, data_15_22042.2]

/-- Complete interval computation for depth 15, residue 22043. -/
theorem bounds_15_22043 : exactInterval 15 22043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22043 : oddCount 22043 15 = 11 ∧ acceleratedOrbit 15 22043 = 119177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22043) = 3 ^ 11 * m + 119177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22043.1, data_15_22043.2]

/-- Complete interval computation for depth 15, residue 22044. -/
theorem bounds_15_22044 : exactInterval 15 22044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22044 : oddCount 22044 15 = 5 ∧ acceleratedOrbit 15 22044 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22044) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22044.1, data_15_22044.2]

/-- Complete interval computation for depth 15, residue 22045. -/
theorem bounds_15_22045 : exactInterval 15 22045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22045 : oddCount 22045 15 = 5 ∧ acceleratedOrbit 15 22045 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22045) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22045.1, data_15_22045.2]

/-- Complete interval computation for depth 15, residue 22046. -/
theorem bounds_15_22046 : exactInterval 15 22046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22046 : oddCount 22046 15 = 5 ∧ acceleratedOrbit 15 22046 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22046) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22046.1, data_15_22046.2]

/-- Complete interval computation for depth 15, residue 22047. -/
theorem bounds_15_22047 : exactInterval 15 22047 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22047) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22047 : oddCount 22047 15 = 9 ∧ acceleratedOrbit 15 22047 = 13244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22047) = 3 ^ 9 * m + 13244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22047.1, data_15_22047.2]

/-- Complete interval computation for depth 15, residue 22048. -/
theorem bounds_15_22048 : exactInterval 15 22048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22048 : oddCount 22048 15 = 4 ∧ acceleratedOrbit 15 22048 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22048) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22048.1, data_15_22048.2]

/-- Complete interval computation for depth 15, residue 22049. -/
theorem bounds_15_22049 : exactInterval 15 22049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22049 : oddCount 22049 15 = 7 ∧ acceleratedOrbit 15 22049 = 1472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22049) = 3 ^ 7 * m + 1472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22049.1, data_15_22049.2]

/-- Complete interval computation for depth 15, residue 22050. -/
theorem bounds_15_22050 : exactInterval 15 22050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22050 : oddCount 22050 15 = 6 ∧ acceleratedOrbit 15 22050 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22050) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22050.1, data_15_22050.2]

/-- Complete interval computation for depth 15, residue 22051. -/
theorem bounds_15_22051 : exactInterval 15 22051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22051 : oddCount 22051 15 = 6 ∧ acceleratedOrbit 15 22051 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22051) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22051.1, data_15_22051.2]

end Collatz.Research.PassageAtlas.Batch0673
