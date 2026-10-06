import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0199

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 2017. -/
theorem bounds_11_2017 : exactInterval 11 2017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2017 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2017) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2017 : oddCount 2017 11 = 8 ∧ acceleratedOrbit 11 2017 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2017 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2017) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2017.1, data_11_2017.2]

/-- Complete interval computation for depth 11, residue 2018. -/
theorem bounds_11_2018 : exactInterval 11 2018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2018 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2018) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2018 : oddCount 2018 11 = 5 ∧ acceleratedOrbit 11 2018 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2018 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2018) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2018.1, data_11_2018.2]

/-- Complete interval computation for depth 11, residue 2019. -/
theorem bounds_11_2019 : exactInterval 11 2019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2019 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2019) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2019 : oddCount 2019 11 = 5 ∧ acceleratedOrbit 11 2019 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2019 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2019) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2019.1, data_11_2019.2]

/-- Complete interval computation for depth 11, residue 2020. -/
theorem bounds_11_2020 : exactInterval 11 2020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2020 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2020) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2020 : oddCount 2020 11 = 6 ∧ acceleratedOrbit 11 2020 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2020 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2020) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2020.1, data_11_2020.2]

/-- Complete interval computation for depth 11, residue 2021. -/
theorem bounds_11_2021 : exactInterval 11 2021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2021 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2021) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2021 : oddCount 2021 11 = 6 ∧ acceleratedOrbit 11 2021 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2021 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2021) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2021.1, data_11_2021.2]

/-- Complete interval computation for depth 11, residue 2022. -/
theorem bounds_11_2022 : exactInterval 11 2022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2022 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2022) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2022 : oddCount 2022 11 = 6 ∧ acceleratedOrbit 11 2022 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2022 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2022) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2022.1, data_11_2022.2]

/-- Complete interval computation for depth 11, residue 2023. -/
theorem bounds_11_2023 : exactInterval 11 2023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2023 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2023) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2023 : oddCount 2023 11 = 7 ∧ acceleratedOrbit 11 2023 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2023 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2023) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2023.1, data_11_2023.2]

/-- Complete interval computation for depth 11, residue 2024. -/
theorem bounds_11_2024 : exactInterval 11 2024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2024 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2024) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2024 : oddCount 2024 11 = 6 ∧ acceleratedOrbit 11 2024 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2024 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2024) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2024.1, data_11_2024.2]

/-- Complete interval computation for depth 11, residue 2025. -/
theorem bounds_11_2025 : exactInterval 11 2025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2025 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2025) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2025 : oddCount 2025 11 = 8 ∧ acceleratedOrbit 11 2025 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2025 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2025) = 3 ^ 8 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2025.1, data_11_2025.2]

/-- Complete interval computation for depth 11, residue 2026. -/
theorem bounds_11_2026 : exactInterval 11 2026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2026 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2026) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2026 : oddCount 2026 11 = 6 ∧ acceleratedOrbit 11 2026 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2026 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2026) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2026.1, data_11_2026.2]

/-- Complete interval computation for depth 11, residue 2027. -/
theorem bounds_11_2027 : exactInterval 11 2027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2027 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2027) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2027 : oddCount 2027 11 = 8 ∧ acceleratedOrbit 11 2027 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2027 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2027) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2027.1, data_11_2027.2]

/-- Complete interval computation for depth 11, residue 2028. -/
theorem bounds_11_2028 : exactInterval 11 2028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2028 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2028) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2028 : oddCount 2028 11 = 6 ∧ acceleratedOrbit 11 2028 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2028 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2028) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2028.1, data_11_2028.2]

/-- Complete interval computation for depth 11, residue 2029. -/
theorem bounds_11_2029 : exactInterval 11 2029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2029 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2029) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2029 : oddCount 2029 11 = 6 ∧ acceleratedOrbit 11 2029 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2029 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2029) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2029.1, data_11_2029.2]

/-- Complete interval computation for depth 11, residue 2030. -/
theorem bounds_11_2030 : exactInterval 11 2030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2030 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2030) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2030 : oddCount 2030 11 = 6 ∧ acceleratedOrbit 11 2030 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2030 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2030) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2030.1, data_11_2030.2]

/-- Complete interval computation for depth 11, residue 2031. -/
theorem bounds_11_2031 : exactInterval 11 2031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2031 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2031) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2031 : oddCount 2031 11 = 7 ∧ acceleratedOrbit 11 2031 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2031 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2031) = 3 ^ 7 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2031.1, data_11_2031.2]

end Collatz.Research.StoppingAtlas.Batch0199
