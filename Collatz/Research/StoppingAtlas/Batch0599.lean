import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0599

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2017. -/
theorem bounds_13_2017 : exactInterval 13 2017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2017 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2017) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2017 : oddCount 2017 13 = 9 ∧ acceleratedOrbit 13 2017 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2017 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2017) = 3 ^ 9 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2017.1, data_13_2017.2]

/-- Complete interval computation for depth 13, residue 2018. -/
theorem bounds_13_2018 : exactInterval 13 2018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2018 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2018) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2018 : oddCount 2018 13 = 6 ∧ acceleratedOrbit 13 2018 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2018 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2018) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2018.1, data_13_2018.2]

/-- Complete interval computation for depth 13, residue 2019. -/
theorem bounds_13_2019 : exactInterval 13 2019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2019 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2019) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2019 : oddCount 2019 13 = 6 ∧ acceleratedOrbit 13 2019 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2019 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2019) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2019.1, data_13_2019.2]

/-- Complete interval computation for depth 13, residue 2020. -/
theorem bounds_13_2020 : exactInterval 13 2020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2020 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2020) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2020 : oddCount 2020 13 = 7 ∧ acceleratedOrbit 13 2020 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2020 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2020) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2020.1, data_13_2020.2]

/-- Complete interval computation for depth 13, residue 2021. -/
theorem bounds_13_2021 : exactInterval 13 2021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2021 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2021) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2021 : oddCount 2021 13 = 7 ∧ acceleratedOrbit 13 2021 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2021 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2021) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2021.1, data_13_2021.2]

/-- Complete interval computation for depth 13, residue 2022. -/
theorem bounds_13_2022 : exactInterval 13 2022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2022 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2022) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2022 : oddCount 2022 13 = 7 ∧ acceleratedOrbit 13 2022 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2022 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2022) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2022.1, data_13_2022.2]

/-- Complete interval computation for depth 13, residue 2023. -/
theorem bounds_13_2023 : exactInterval 13 2023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2023 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2023) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2023 : oddCount 2023 13 = 8 ∧ acceleratedOrbit 13 2023 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2023 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2023) = 3 ^ 8 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2023.1, data_13_2023.2]

/-- Complete interval computation for depth 13, residue 2024. -/
theorem bounds_13_2024 : exactInterval 13 2024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2024 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2024) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2024 : oddCount 2024 13 = 6 ∧ acceleratedOrbit 13 2024 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2024 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2024) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2024.1, data_13_2024.2]

/-- Complete interval computation for depth 13, residue 2025. -/
theorem bounds_13_2025 : exactInterval 13 2025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2025 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2025) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2025 : oddCount 2025 13 = 9 ∧ acceleratedOrbit 13 2025 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2025 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2025) = 3 ^ 9 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2025.1, data_13_2025.2]

/-- Complete interval computation for depth 13, residue 2026. -/
theorem bounds_13_2026 : exactInterval 13 2026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2026 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2026) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2026 : oddCount 2026 13 = 6 ∧ acceleratedOrbit 13 2026 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2026 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2026) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2026.1, data_13_2026.2]

/-- Complete interval computation for depth 13, residue 2027. -/
theorem bounds_13_2027 : exactInterval 13 2027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2027 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2027) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2027 : oddCount 2027 13 = 8 ∧ acceleratedOrbit 13 2027 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2027 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2027) = 3 ^ 8 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2027.1, data_13_2027.2]

/-- Complete interval computation for depth 13, residue 2028. -/
theorem bounds_13_2028 : exactInterval 13 2028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2028 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2028) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2028 : oddCount 2028 13 = 6 ∧ acceleratedOrbit 13 2028 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2028 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2028) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2028.1, data_13_2028.2]

/-- Complete interval computation for depth 13, residue 2029. -/
theorem bounds_13_2029 : exactInterval 13 2029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2029 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2029) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2029 : oddCount 2029 13 = 6 ∧ acceleratedOrbit 13 2029 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2029 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2029) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2029.1, data_13_2029.2]

/-- Complete interval computation for depth 13, residue 2030. -/
theorem bounds_13_2030 : exactInterval 13 2030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2030 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2030) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2030 : oddCount 2030 13 = 6 ∧ acceleratedOrbit 13 2030 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2030 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2030) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2030.1, data_13_2030.2]

/-- Complete interval computation for depth 13, residue 2031. -/
theorem bounds_13_2031 : exactInterval 13 2031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2031 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2031) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2031 : oddCount 2031 13 = 8 ∧ acceleratedOrbit 13 2031 = 1628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2031 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2031) = 3 ^ 8 * m + 1628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2031.1, data_13_2031.2]

end Collatz.Research.StoppingAtlas.Batch0599
