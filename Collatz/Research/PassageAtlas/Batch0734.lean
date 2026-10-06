import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0734

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24018. -/
theorem bounds_15_24018 : exactInterval 15 24018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24018 : oddCount 24018 15 = 8 ∧ acceleratedOrbit 15 24018 = 4810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24018) = 3 ^ 8 * m + 4810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24018.1, data_15_24018.2]

/-- Complete interval computation for depth 15, residue 24019. -/
theorem bounds_15_24019 : exactInterval 15 24019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24019 : oddCount 24019 15 = 8 ∧ acceleratedOrbit 15 24019 = 4810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24019) = 3 ^ 8 * m + 4810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24019.1, data_15_24019.2]

/-- Complete interval computation for depth 15, residue 24020. -/
theorem bounds_15_24020 : exactInterval 15 24020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24020 : oddCount 24020 15 = 5 ∧ acceleratedOrbit 15 24020 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24020) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24020.1, data_15_24020.2]

/-- Complete interval computation for depth 15, residue 24021. -/
theorem bounds_15_24021 : exactInterval 15 24021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24021 : oddCount 24021 15 = 5 ∧ acceleratedOrbit 15 24021 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24021) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24021.1, data_15_24021.2]

/-- Complete interval computation for depth 15, residue 24022. -/
theorem bounds_15_24022 : exactInterval 15 24022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24022 : oddCount 24022 15 = 7 ∧ acceleratedOrbit 15 24022 = 1604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24022) = 3 ^ 7 * m + 1604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24022.1, data_15_24022.2]

/-- Complete interval computation for depth 15, residue 24023. -/
theorem bounds_15_24023 : exactInterval 15 24023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24023 : oddCount 24023 15 = 7 ∧ acceleratedOrbit 15 24023 = 1604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24023) = 3 ^ 7 * m + 1604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24023.1, data_15_24023.2]

/-- Complete interval computation for depth 15, residue 24024. -/
theorem bounds_15_24024 : exactInterval 15 24024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24024 : oddCount 24024 15 = 6 ∧ acceleratedOrbit 15 24024 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24024) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24024.1, data_15_24024.2]

/-- Complete interval computation for depth 15, residue 24025. -/
theorem bounds_15_24025 : exactInterval 15 24025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24025 : oddCount 24025 15 = 6 ∧ acceleratedOrbit 15 24025 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24025) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24025.1, data_15_24025.2]

/-- Complete interval computation for depth 15, residue 24026. -/
theorem bounds_15_24026 : exactInterval 15 24026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24026 : oddCount 24026 15 = 6 ∧ acceleratedOrbit 15 24026 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24026) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24026.1, data_15_24026.2]

/-- Complete interval computation for depth 15, residue 24027. -/
theorem bounds_15_24027 : exactInterval 15 24027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24027 : oddCount 24027 15 = 7 ∧ acceleratedOrbit 15 24027 = 1604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24027) = 3 ^ 7 * m + 1604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24027.1, data_15_24027.2]

/-- Complete interval computation for depth 15, residue 24028. -/
theorem bounds_15_24028 : exactInterval 15 24028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24028 : oddCount 24028 15 = 6 ∧ acceleratedOrbit 15 24028 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24028) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24028.1, data_15_24028.2]

/-- Complete interval computation for depth 15, residue 24029. -/
theorem bounds_15_24029 : exactInterval 15 24029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24029 : oddCount 24029 15 = 6 ∧ acceleratedOrbit 15 24029 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24029) = 3 ^ 6 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24029.1, data_15_24029.2]

/-- Complete interval computation for depth 15, residue 24030. -/
theorem bounds_15_24030 : exactInterval 15 24030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24030 : oddCount 24030 15 = 11 ∧ acceleratedOrbit 15 24030 = 129923 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24030) = 3 ^ 11 * m + 129923 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24030.1, data_15_24030.2]

/-- Complete interval computation for depth 15, residue 24031. -/
theorem bounds_15_24031 : exactInterval 15 24031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24031 : oddCount 24031 15 = 11 ∧ acceleratedOrbit 15 24031 = 129923 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24031) = 3 ^ 11 * m + 129923 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24031.1, data_15_24031.2]

/-- Complete interval computation for depth 15, residue 24032. -/
theorem bounds_15_24032 : exactInterval 15 24032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24032 : oddCount 24032 15 = 8 ∧ acceleratedOrbit 15 24032 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24032) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24032.1, data_15_24032.2]

/-- Complete interval computation for depth 15, residue 24033. -/
theorem bounds_15_24033 : exactInterval 15 24033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24033 : oddCount 24033 15 = 9 ∧ acceleratedOrbit 15 24033 = 14438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24033) = 3 ^ 9 * m + 14438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24033.1, data_15_24033.2]

/-- Complete interval computation for depth 15, residue 24034. -/
theorem bounds_15_24034 : exactInterval 15 24034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24034 : oddCount 24034 15 = 5 ∧ acceleratedOrbit 15 24034 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24034) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24034.1, data_15_24034.2]

/-- Complete interval computation for depth 15, residue 24035. -/
theorem bounds_15_24035 : exactInterval 15 24035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24035 : oddCount 24035 15 = 5 ∧ acceleratedOrbit 15 24035 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24035) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24035.1, data_15_24035.2]

/-- Complete interval computation for depth 15, residue 24036. -/
theorem bounds_15_24036 : exactInterval 15 24036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24036 : oddCount 24036 15 = 9 ∧ acceleratedOrbit 15 24036 = 14444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24036) = 3 ^ 9 * m + 14444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24036.1, data_15_24036.2]

/-- Complete interval computation for depth 15, residue 24037. -/
theorem bounds_15_24037 : exactInterval 15 24037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24037 : oddCount 24037 15 = 9 ∧ acceleratedOrbit 15 24037 = 14444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24037) = 3 ^ 9 * m + 14444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24037.1, data_15_24037.2]

/-- Complete interval computation for depth 15, residue 24038. -/
theorem bounds_15_24038 : exactInterval 15 24038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24038 : oddCount 24038 15 = 9 ∧ acceleratedOrbit 15 24038 = 14444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24038) = 3 ^ 9 * m + 14444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24038.1, data_15_24038.2]

/-- Complete interval computation for depth 15, residue 24039. -/
theorem bounds_15_24039 : exactInterval 15 24039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24039 : oddCount 24039 15 = 8 ∧ acceleratedOrbit 15 24039 = 4814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24039) = 3 ^ 8 * m + 4814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24039.1, data_15_24039.2]

/-- Complete interval computation for depth 15, residue 24040. -/
theorem bounds_15_24040 : exactInterval 15 24040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24040 : oddCount 24040 15 = 8 ∧ acceleratedOrbit 15 24040 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24040) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24040.1, data_15_24040.2]

/-- Complete interval computation for depth 15, residue 24041. -/
theorem bounds_15_24041 : exactInterval 15 24041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24041 : oddCount 24041 15 = 8 ∧ acceleratedOrbit 15 24041 = 4814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24041) = 3 ^ 8 * m + 4814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24041.1, data_15_24041.2]

/-- Complete interval computation for depth 15, residue 24042. -/
theorem bounds_15_24042 : exactInterval 15 24042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24042 : oddCount 24042 15 = 8 ∧ acceleratedOrbit 15 24042 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24042) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24042.1, data_15_24042.2]

/-- Complete interval computation for depth 15, residue 24043. -/
theorem bounds_15_24043 : exactInterval 15 24043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24043 : oddCount 24043 15 = 10 ∧ acceleratedOrbit 15 24043 = 43330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24043) = 3 ^ 10 * m + 43330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24043.1, data_15_24043.2]

/-- Complete interval computation for depth 15, residue 24044. -/
theorem bounds_15_24044 : exactInterval 15 24044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24044 : oddCount 24044 15 = 8 ∧ acceleratedOrbit 15 24044 = 4816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24044) = 3 ^ 8 * m + 4816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24044.1, data_15_24044.2]

/-- Complete interval computation for depth 15, residue 24045. -/
theorem bounds_15_24045 : exactInterval 15 24045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24045 : oddCount 24045 15 = 8 ∧ acceleratedOrbit 15 24045 = 4816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24045) = 3 ^ 8 * m + 4816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24045.1, data_15_24045.2]

/-- Complete interval computation for depth 15, residue 24046. -/
theorem bounds_15_24046 : exactInterval 15 24046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24046 : oddCount 24046 15 = 8 ∧ acceleratedOrbit 15 24046 = 4816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24046) = 3 ^ 8 * m + 4816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24046.1, data_15_24046.2]

/-- Complete interval computation for depth 15, residue 24047. -/
theorem bounds_15_24047 : exactInterval 15 24047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24047 : oddCount 24047 15 = 10 ∧ acceleratedOrbit 15 24047 = 43336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24047) = 3 ^ 10 * m + 43336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24047.1, data_15_24047.2]

/-- Complete interval computation for depth 15, residue 24048. -/
theorem bounds_15_24048 : exactInterval 15 24048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24048 : oddCount 24048 15 = 8 ∧ acceleratedOrbit 15 24048 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24048) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24048.1, data_15_24048.2]

/-- Complete interval computation for depth 15, residue 24049. -/
theorem bounds_15_24049 : exactInterval 15 24049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24049 : oddCount 24049 15 = 8 ∧ acceleratedOrbit 15 24049 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24049) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24049.1, data_15_24049.2]

/-- Complete interval computation for depth 15, residue 24050. -/
theorem bounds_15_24050 : exactInterval 15 24050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24050 : oddCount 24050 15 = 7 ∧ acceleratedOrbit 15 24050 = 1606 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24050) = 3 ^ 7 * m + 1606 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24050.1, data_15_24050.2]

end Collatz.Research.PassageAtlas.Batch0734
