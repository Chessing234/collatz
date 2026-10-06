import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0332

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2012. -/
theorem bounds_12_2012 : exactInterval 12 2012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2012 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2012) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2012 : oddCount 2012 12 = 7 ∧ acceleratedOrbit 12 2012 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2012 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2012) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2012.1, data_12_2012.2]

/-- Complete interval computation for depth 12, residue 2013. -/
theorem bounds_12_2013 : exactInterval 12 2013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2013 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2013) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2013 : oddCount 2013 12 = 7 ∧ acceleratedOrbit 12 2013 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2013 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2013) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2013.1, data_12_2013.2]

/-- Complete interval computation for depth 12, residue 2014. -/
theorem bounds_12_2014 : exactInterval 12 2014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2014 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2014) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2014 : oddCount 2014 12 = 8 ∧ acceleratedOrbit 12 2014 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2014 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2014) = 3 ^ 8 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2014.1, data_12_2014.2]

/-- Complete interval computation for depth 12, residue 2015. -/
theorem bounds_12_2015 : exactInterval 12 2015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2015 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2015) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2015 : oddCount 2015 12 = 8 ∧ acceleratedOrbit 12 2015 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2015 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2015) = 3 ^ 8 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2015.1, data_12_2015.2]

/-- Complete interval computation for depth 12, residue 2016. -/
theorem bounds_12_2016 : exactInterval 12 2016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2016 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2016) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2016 : oddCount 2016 12 = 6 ∧ acceleratedOrbit 12 2016 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2016 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2016) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2016.1, data_12_2016.2]

/-- Complete interval computation for depth 12, residue 2017. -/
theorem bounds_12_2017 : exactInterval 12 2017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2017 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2017) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2017 : oddCount 2017 12 = 8 ∧ acceleratedOrbit 12 2017 = 3235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2017 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2017) = 3 ^ 8 * m + 3235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2017.1, data_12_2017.2]

/-- Complete interval computation for depth 12, residue 2018. -/
theorem bounds_12_2018 : exactInterval 12 2018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2018 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2018) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2018 : oddCount 2018 12 = 5 ∧ acceleratedOrbit 12 2018 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2018 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2018) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2018.1, data_12_2018.2]

/-- Complete interval computation for depth 12, residue 2019. -/
theorem bounds_12_2019 : exactInterval 12 2019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2019 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2019) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2019 : oddCount 2019 12 = 5 ∧ acceleratedOrbit 12 2019 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2019 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2019) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2019.1, data_12_2019.2]

/-- Complete interval computation for depth 12, residue 2020. -/
theorem bounds_12_2020 : exactInterval 12 2020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2020 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2020) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2020 : oddCount 2020 12 = 6 ∧ acceleratedOrbit 12 2020 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2020 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2020) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2020.1, data_12_2020.2]

/-- Complete interval computation for depth 12, residue 2021. -/
theorem bounds_12_2021 : exactInterval 12 2021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2021 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2021) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2021 : oddCount 2021 12 = 6 ∧ acceleratedOrbit 12 2021 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2021 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2021) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2021.1, data_12_2021.2]

/-- Complete interval computation for depth 12, residue 2022. -/
theorem bounds_12_2022 : exactInterval 12 2022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2022 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2022) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2022 : oddCount 2022 12 = 6 ∧ acceleratedOrbit 12 2022 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2022 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2022) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2022.1, data_12_2022.2]

/-- Complete interval computation for depth 12, residue 2023. -/
theorem bounds_12_2023 : exactInterval 12 2023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2023 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2023) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2023 : oddCount 2023 12 = 7 ∧ acceleratedOrbit 12 2023 = 1081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2023 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2023) = 3 ^ 7 * m + 1081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2023.1, data_12_2023.2]

/-- Complete interval computation for depth 12, residue 2024. -/
theorem bounds_12_2024 : exactInterval 12 2024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2024 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2024) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2024 : oddCount 2024 12 = 6 ∧ acceleratedOrbit 12 2024 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2024 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2024) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2024.1, data_12_2024.2]

/-- Complete interval computation for depth 12, residue 2025. -/
theorem bounds_12_2025 : exactInterval 12 2025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2025 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2025) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2025 : oddCount 2025 12 = 9 ∧ acceleratedOrbit 12 2025 = 9740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2025 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2025) = 3 ^ 9 * m + 9740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2025.1, data_12_2025.2]

/-- Complete interval computation for depth 12, residue 2026. -/
theorem bounds_12_2026 : exactInterval 12 2026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2026 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2026) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2026 : oddCount 2026 12 = 6 ∧ acceleratedOrbit 12 2026 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2026 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2026) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2026.1, data_12_2026.2]

end Collatz.Research.StoppingAtlas.Batch0332
