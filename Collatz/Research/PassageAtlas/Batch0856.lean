import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0856

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28016. -/
theorem bounds_15_28016 : exactInterval 15 28016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28016 : oddCount 28016 15 = 5 ∧ acceleratedOrbit 15 28016 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28016) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28016.1, data_15_28016.2]

/-- Complete interval computation for depth 15, residue 28017. -/
theorem bounds_15_28017 : exactInterval 15 28017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28017 : oddCount 28017 15 = 5 ∧ acceleratedOrbit 15 28017 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28017) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28017.1, data_15_28017.2]

/-- Complete interval computation for depth 15, residue 28018. -/
theorem bounds_15_28018 : exactInterval 15 28018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28018 : oddCount 28018 15 = 7 ∧ acceleratedOrbit 15 28018 = 1871 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28018) = 3 ^ 7 * m + 1871 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28018.1, data_15_28018.2]

/-- Complete interval computation for depth 15, residue 28019. -/
theorem bounds_15_28019 : exactInterval 15 28019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28019 : oddCount 28019 15 = 7 ∧ acceleratedOrbit 15 28019 = 1871 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28019) = 3 ^ 7 * m + 1871 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28019.1, data_15_28019.2]

/-- Complete interval computation for depth 15, residue 28020. -/
theorem bounds_15_28020 : exactInterval 15 28020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28020 : oddCount 28020 15 = 5 ∧ acceleratedOrbit 15 28020 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28020) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28020.1, data_15_28020.2]

/-- Complete interval computation for depth 15, residue 28021. -/
theorem bounds_15_28021 : exactInterval 15 28021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28021 : oddCount 28021 15 = 5 ∧ acceleratedOrbit 15 28021 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28021) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28021.1, data_15_28021.2]

/-- Complete interval computation for depth 15, residue 28022. -/
theorem bounds_15_28022 : exactInterval 15 28022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28022 : oddCount 28022 15 = 7 ∧ acceleratedOrbit 15 28022 = 1871 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28022) = 3 ^ 7 * m + 1871 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28022.1, data_15_28022.2]

/-- Complete interval computation for depth 15, residue 28023. -/
theorem bounds_15_28023 : exactInterval 15 28023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28023 : oddCount 28023 15 = 7 ∧ acceleratedOrbit 15 28023 = 1871 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28023) = 3 ^ 7 * m + 1871 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28023.1, data_15_28023.2]

/-- Complete interval computation for depth 15, residue 28024. -/
theorem bounds_15_28024 : exactInterval 15 28024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28024 : oddCount 28024 15 = 8 ∧ acceleratedOrbit 15 28024 = 5615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28024) = 3 ^ 8 * m + 5615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28024.1, data_15_28024.2]

/-- Complete interval computation for depth 15, residue 28025. -/
theorem bounds_15_28025 : exactInterval 15 28025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28025 : oddCount 28025 15 = 10 ∧ acceleratedOrbit 15 28025 = 50507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28025) = 3 ^ 10 * m + 50507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28025.1, data_15_28025.2]

/-- Complete interval computation for depth 15, residue 28026. -/
theorem bounds_15_28026 : exactInterval 15 28026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28026 : oddCount 28026 15 = 8 ∧ acceleratedOrbit 15 28026 = 5615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28026) = 3 ^ 8 * m + 5615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28026.1, data_15_28026.2]

/-- Complete interval computation for depth 15, residue 28027. -/
theorem bounds_15_28027 : exactInterval 15 28027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28027 : oddCount 28027 15 = 9 ∧ acceleratedOrbit 15 28027 = 16838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28027) = 3 ^ 9 * m + 16838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28027.1, data_15_28027.2]

/-- Complete interval computation for depth 15, residue 28028. -/
theorem bounds_15_28028 : exactInterval 15 28028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28028 : oddCount 28028 15 = 8 ∧ acceleratedOrbit 15 28028 = 5615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28028) = 3 ^ 8 * m + 5615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28028.1, data_15_28028.2]

/-- Complete interval computation for depth 15, residue 28029. -/
theorem bounds_15_28029 : exactInterval 15 28029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28029 : oddCount 28029 15 = 8 ∧ acceleratedOrbit 15 28029 = 5615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28029) = 3 ^ 8 * m + 5615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28029.1, data_15_28029.2]

/-- Complete interval computation for depth 15, residue 28030. -/
theorem bounds_15_28030 : exactInterval 15 28030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28030 : oddCount 28030 15 = 10 ∧ acceleratedOrbit 15 28030 = 50516 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28030) = 3 ^ 10 * m + 50516 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28030.1, data_15_28030.2]

/-- Complete interval computation for depth 15, residue 28031. -/
theorem bounds_15_28031 : exactInterval 15 28031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28031 : oddCount 28031 15 = 10 ∧ acceleratedOrbit 15 28031 = 50516 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28031) = 3 ^ 10 * m + 50516 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28031.1, data_15_28031.2]

/-- Complete interval computation for depth 15, residue 28032. -/
theorem bounds_15_28032 : exactInterval 15 28032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28032 : oddCount 28032 15 = 5 ∧ acceleratedOrbit 15 28032 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28032) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28032.1, data_15_28032.2]

/-- Complete interval computation for depth 15, residue 28033. -/
theorem bounds_15_28033 : exactInterval 15 28033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28033 : oddCount 28033 15 = 8 ∧ acceleratedOrbit 15 28033 = 5615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28033) = 3 ^ 8 * m + 5615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28033.1, data_15_28033.2]

/-- Complete interval computation for depth 15, residue 28034. -/
theorem bounds_15_28034 : exactInterval 15 28034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28034 : oddCount 28034 15 = 5 ∧ acceleratedOrbit 15 28034 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28034) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28034.1, data_15_28034.2]

/-- Complete interval computation for depth 15, residue 28035. -/
theorem bounds_15_28035 : exactInterval 15 28035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28035 : oddCount 28035 15 = 5 ∧ acceleratedOrbit 15 28035 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28035) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28035.1, data_15_28035.2]

/-- Complete interval computation for depth 15, residue 28036. -/
theorem bounds_15_28036 : exactInterval 15 28036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28036 : oddCount 28036 15 = 10 ∧ acceleratedOrbit 15 28036 = 50543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28036) = 3 ^ 10 * m + 50543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28036.1, data_15_28036.2]

/-- Complete interval computation for depth 15, residue 28037. -/
theorem bounds_15_28037 : exactInterval 15 28037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28037 : oddCount 28037 15 = 10 ∧ acceleratedOrbit 15 28037 = 50543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28037) = 3 ^ 10 * m + 50543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28037.1, data_15_28037.2]

/-- Complete interval computation for depth 15, residue 28038. -/
theorem bounds_15_28038 : exactInterval 15 28038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28038 : oddCount 28038 15 = 10 ∧ acceleratedOrbit 15 28038 = 50543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28038) = 3 ^ 10 * m + 50543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28038.1, data_15_28038.2]

/-- Complete interval computation for depth 15, residue 28039. -/
theorem bounds_15_28039 : exactInterval 15 28039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28039 : oddCount 28039 15 = 5 ∧ acceleratedOrbit 15 28039 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28039) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28039.1, data_15_28039.2]

/-- Complete interval computation for depth 15, residue 28040. -/
theorem bounds_15_28040 : exactInterval 15 28040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28040 : oddCount 28040 15 = 5 ∧ acceleratedOrbit 15 28040 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28040) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28040.1, data_15_28040.2]

/-- Complete interval computation for depth 15, residue 28041. -/
theorem bounds_15_28041 : exactInterval 15 28041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28041 : oddCount 28041 15 = 9 ∧ acceleratedOrbit 15 28041 = 16847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28041) = 3 ^ 9 * m + 16847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28041.1, data_15_28041.2]

/-- Complete interval computation for depth 15, residue 28042. -/
theorem bounds_15_28042 : exactInterval 15 28042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28042 : oddCount 28042 15 = 5 ∧ acceleratedOrbit 15 28042 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28042) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28042.1, data_15_28042.2]

/-- Complete interval computation for depth 15, residue 28043. -/
theorem bounds_15_28043 : exactInterval 15 28043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28043 : oddCount 28043 15 = 10 ∧ acceleratedOrbit 15 28043 = 50543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28043) = 3 ^ 10 * m + 50543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28043.1, data_15_28043.2]

/-- Complete interval computation for depth 15, residue 28044. -/
theorem bounds_15_28044 : exactInterval 15 28044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28044 : oddCount 28044 15 = 5 ∧ acceleratedOrbit 15 28044 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28044) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28044.1, data_15_28044.2]

/-- Complete interval computation for depth 15, residue 28045. -/
theorem bounds_15_28045 : exactInterval 15 28045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28045 : oddCount 28045 15 = 5 ∧ acceleratedOrbit 15 28045 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28045) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28045.1, data_15_28045.2]

/-- Complete interval computation for depth 15, residue 28046. -/
theorem bounds_15_28046 : exactInterval 15 28046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28046 : oddCount 28046 15 = 5 ∧ acceleratedOrbit 15 28046 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28046) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28046.1, data_15_28046.2]

/-- Complete interval computation for depth 15, residue 28047. -/
theorem bounds_15_28047 : exactInterval 15 28047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28047 : oddCount 28047 15 = 5 ∧ acceleratedOrbit 15 28047 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28047) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28047.1, data_15_28047.2]

/-- Complete interval computation for depth 15, residue 28048. -/
theorem bounds_15_28048 : exactInterval 15 28048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28048 : oddCount 28048 15 = 5 ∧ acceleratedOrbit 15 28048 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28048) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28048.1, data_15_28048.2]

end Collatz.Research.PassageAtlas.Batch0856
