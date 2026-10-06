import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0978

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32014. -/
theorem bounds_15_32014 : exactInterval 15 32014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32014 : oddCount 32014 15 = 8 ∧ acceleratedOrbit 15 32014 = 6412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32014) = 3 ^ 8 * m + 6412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32014.1, data_15_32014.2]

/-- Complete interval computation for depth 15, residue 32015. -/
theorem bounds_15_32015 : exactInterval 15 32015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32015 : oddCount 32015 15 = 8 ∧ acceleratedOrbit 15 32015 = 6412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32015) = 3 ^ 8 * m + 6412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32015.1, data_15_32015.2]

/-- Complete interval computation for depth 15, residue 32016. -/
theorem bounds_15_32016 : exactInterval 15 32016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32016 : oddCount 32016 15 = 5 ∧ acceleratedOrbit 15 32016 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32016) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32016.1, data_15_32016.2]

/-- Complete interval computation for depth 15, residue 32017. -/
theorem bounds_15_32017 : exactInterval 15 32017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32017 : oddCount 32017 15 = 6 ∧ acceleratedOrbit 15 32017 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32017) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32017.1, data_15_32017.2]

/-- Complete interval computation for depth 15, residue 32018. -/
theorem bounds_15_32018 : exactInterval 15 32018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32018 : oddCount 32018 15 = 9 ∧ acceleratedOrbit 15 32018 = 19235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32018) = 3 ^ 9 * m + 19235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32018.1, data_15_32018.2]

/-- Complete interval computation for depth 15, residue 32019. -/
theorem bounds_15_32019 : exactInterval 15 32019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32019 : oddCount 32019 15 = 9 ∧ acceleratedOrbit 15 32019 = 19235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32019) = 3 ^ 9 * m + 19235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32019.1, data_15_32019.2]

/-- Complete interval computation for depth 15, residue 32020. -/
theorem bounds_15_32020 : exactInterval 15 32020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32020 : oddCount 32020 15 = 5 ∧ acceleratedOrbit 15 32020 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32020) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32020.1, data_15_32020.2]

/-- Complete interval computation for depth 15, residue 32021. -/
theorem bounds_15_32021 : exactInterval 15 32021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32021 : oddCount 32021 15 = 5 ∧ acceleratedOrbit 15 32021 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32021) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32021.1, data_15_32021.2]

/-- Complete interval computation for depth 15, residue 32022. -/
theorem bounds_15_32022 : exactInterval 15 32022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32022 : oddCount 32022 15 = 6 ∧ acceleratedOrbit 15 32022 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32022) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32022.1, data_15_32022.2]

/-- Complete interval computation for depth 15, residue 32023. -/
theorem bounds_15_32023 : exactInterval 15 32023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32023 : oddCount 32023 15 = 6 ∧ acceleratedOrbit 15 32023 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32023) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32023.1, data_15_32023.2]

/-- Complete interval computation for depth 15, residue 32024. -/
theorem bounds_15_32024 : exactInterval 15 32024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32024 : oddCount 32024 15 = 5 ∧ acceleratedOrbit 15 32024 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32024) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32024.1, data_15_32024.2]

/-- Complete interval computation for depth 15, residue 32025. -/
theorem bounds_15_32025 : exactInterval 15 32025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32025 : oddCount 32025 15 = 8 ∧ acceleratedOrbit 15 32025 = 6413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32025) = 3 ^ 8 * m + 6413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32025.1, data_15_32025.2]

/-- Complete interval computation for depth 15, residue 32026. -/
theorem bounds_15_32026 : exactInterval 15 32026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32026 : oddCount 32026 15 = 5 ∧ acceleratedOrbit 15 32026 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32026) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32026.1, data_15_32026.2]

/-- Complete interval computation for depth 15, residue 32027. -/
theorem bounds_15_32027 : exactInterval 15 32027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32027 : oddCount 32027 15 = 11 ∧ acceleratedOrbit 15 32027 = 173150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32027) = 3 ^ 11 * m + 173150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32027.1, data_15_32027.2]

/-- Complete interval computation for depth 15, residue 32028. -/
theorem bounds_15_32028 : exactInterval 15 32028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32028 : oddCount 32028 15 = 7 ∧ acceleratedOrbit 15 32028 = 2138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32028) = 3 ^ 7 * m + 2138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32028.1, data_15_32028.2]

/-- Complete interval computation for depth 15, residue 32029. -/
theorem bounds_15_32029 : exactInterval 15 32029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32029 : oddCount 32029 15 = 7 ∧ acceleratedOrbit 15 32029 = 2138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32029) = 3 ^ 7 * m + 2138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32029.1, data_15_32029.2]

/-- Complete interval computation for depth 15, residue 32030. -/
theorem bounds_15_32030 : exactInterval 15 32030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32030 : oddCount 32030 15 = 7 ∧ acceleratedOrbit 15 32030 = 2138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32030) = 3 ^ 7 * m + 2138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32030.1, data_15_32030.2]

/-- Complete interval computation for depth 15, residue 32031. -/
theorem bounds_15_32031 : exactInterval 15 32031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32031 : oddCount 32031 15 = 7 ∧ acceleratedOrbit 15 32031 = 2138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32031) = 3 ^ 7 * m + 2138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32031.1, data_15_32031.2]

/-- Complete interval computation for depth 15, residue 32032. -/
theorem bounds_15_32032 : exactInterval 15 32032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32032 : oddCount 32032 15 = 8 ∧ acceleratedOrbit 15 32032 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32032) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32032.1, data_15_32032.2]

/-- Complete interval computation for depth 15, residue 32033. -/
theorem bounds_15_32033 : exactInterval 15 32033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32033 : oddCount 32033 15 = 6 ∧ acceleratedOrbit 15 32033 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32033) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32033.1, data_15_32033.2]

/-- Complete interval computation for depth 15, residue 32034. -/
theorem bounds_15_32034 : exactInterval 15 32034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32034 : oddCount 32034 15 = 6 ∧ acceleratedOrbit 15 32034 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32034) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32034.1, data_15_32034.2]

/-- Complete interval computation for depth 15, residue 32035. -/
theorem bounds_15_32035 : exactInterval 15 32035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32035 : oddCount 32035 15 = 6 ∧ acceleratedOrbit 15 32035 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32035) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32035.1, data_15_32035.2]

/-- Complete interval computation for depth 15, residue 32036. -/
theorem bounds_15_32036 : exactInterval 15 32036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32036 : oddCount 32036 15 = 6 ∧ acceleratedOrbit 15 32036 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32036) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32036.1, data_15_32036.2]

/-- Complete interval computation for depth 15, residue 32037. -/
theorem bounds_15_32037 : exactInterval 15 32037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32037 : oddCount 32037 15 = 6 ∧ acceleratedOrbit 15 32037 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32037) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32037.1, data_15_32037.2]

/-- Complete interval computation for depth 15, residue 32038. -/
theorem bounds_15_32038 : exactInterval 15 32038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32038 : oddCount 32038 15 = 6 ∧ acceleratedOrbit 15 32038 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32038) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32038.1, data_15_32038.2]

/-- Complete interval computation for depth 15, residue 32039. -/
theorem bounds_15_32039 : exactInterval 15 32039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32039 : oddCount 32039 15 = 8 ∧ acceleratedOrbit 15 32039 = 6416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32039) = 3 ^ 8 * m + 6416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32039.1, data_15_32039.2]

/-- Complete interval computation for depth 15, residue 32040. -/
theorem bounds_15_32040 : exactInterval 15 32040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32040 : oddCount 32040 15 = 8 ∧ acceleratedOrbit 15 32040 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32040) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32040.1, data_15_32040.2]

/-- Complete interval computation for depth 15, residue 32041. -/
theorem bounds_15_32041 : exactInterval 15 32041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32041 : oddCount 32041 15 = 10 ∧ acceleratedOrbit 15 32041 = 57743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32041) = 3 ^ 10 * m + 57743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32041.1, data_15_32041.2]

/-- Complete interval computation for depth 15, residue 32042. -/
theorem bounds_15_32042 : exactInterval 15 32042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32042 : oddCount 32042 15 = 8 ∧ acceleratedOrbit 15 32042 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32042) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32042.1, data_15_32042.2]

/-- Complete interval computation for depth 15, residue 32043. -/
theorem bounds_15_32043 : exactInterval 15 32043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32043 : oddCount 32043 15 = 10 ∧ acceleratedOrbit 15 32043 = 57752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32043) = 3 ^ 10 * m + 57752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32043.1, data_15_32043.2]

/-- Complete interval computation for depth 15, residue 32044. -/
theorem bounds_15_32044 : exactInterval 15 32044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32044 : oddCount 32044 15 = 5 ∧ acceleratedOrbit 15 32044 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32044) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32044.1, data_15_32044.2]

/-- Complete interval computation for depth 15, residue 32045. -/
theorem bounds_15_32045 : exactInterval 15 32045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32045 : oddCount 32045 15 = 5 ∧ acceleratedOrbit 15 32045 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32045) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32045.1, data_15_32045.2]

/-- Complete interval computation for depth 15, residue 32046. -/
theorem bounds_15_32046 : exactInterval 15 32046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32046 : oddCount 32046 15 = 5 ∧ acceleratedOrbit 15 32046 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32046) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32046.1, data_15_32046.2]

end Collatz.Research.PassageAtlas.Batch0978
