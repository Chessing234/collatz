import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0154

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5013. -/
theorem bounds_15_5013 : exactInterval 15 5013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5013 : oddCount 5013 15 = 7 ∧ acceleratedOrbit 15 5013 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5013) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5013.1, data_15_5013.2]

/-- Complete interval computation for depth 15, residue 5014. -/
theorem bounds_15_5014 : exactInterval 15 5014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5014 : oddCount 5014 15 = 6 ∧ acceleratedOrbit 15 5014 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5014) = 3 ^ 6 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5014.1, data_15_5014.2]

/-- Complete interval computation for depth 15, residue 5015. -/
theorem bounds_15_5015 : exactInterval 15 5015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5015 : oddCount 5015 15 = 6 ∧ acceleratedOrbit 15 5015 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5015) = 3 ^ 6 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5015.1, data_15_5015.2]

/-- Complete interval computation for depth 15, residue 5016. -/
theorem bounds_15_5016 : exactInterval 15 5016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5016 : oddCount 5016 15 = 7 ∧ acceleratedOrbit 15 5016 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5016) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5016.1, data_15_5016.2]

/-- Complete interval computation for depth 15, residue 5017. -/
theorem bounds_15_5017 : exactInterval 15 5017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5017 : oddCount 5017 15 = 6 ∧ acceleratedOrbit 15 5017 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5017) = 3 ^ 6 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5017.1, data_15_5017.2]

/-- Complete interval computation for depth 15, residue 5018. -/
theorem bounds_15_5018 : exactInterval 15 5018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5018 : oddCount 5018 15 = 7 ∧ acceleratedOrbit 15 5018 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5018) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5018.1, data_15_5018.2]

/-- Complete interval computation for depth 15, residue 5019. -/
theorem bounds_15_5019 : exactInterval 15 5019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5019 : oddCount 5019 15 = 9 ∧ acceleratedOrbit 15 5019 = 3017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5019) = 3 ^ 9 * m + 3017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5019.1, data_15_5019.2]

/-- Complete interval computation for depth 15, residue 5020. -/
theorem bounds_15_5020 : exactInterval 15 5020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5020 : oddCount 5020 15 = 9 ∧ acceleratedOrbit 15 5020 = 3019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5020) = 3 ^ 9 * m + 3019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5020.1, data_15_5020.2]

/-- Complete interval computation for depth 15, residue 5021. -/
theorem bounds_15_5021 : exactInterval 15 5021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5021 : oddCount 5021 15 = 9 ∧ acceleratedOrbit 15 5021 = 3019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5021) = 3 ^ 9 * m + 3019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5021.1, data_15_5021.2]

/-- Complete interval computation for depth 15, residue 5022. -/
theorem bounds_15_5022 : exactInterval 15 5022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5022 : oddCount 5022 15 = 9 ∧ acceleratedOrbit 15 5022 = 3019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5022) = 3 ^ 9 * m + 3019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5022.1, data_15_5022.2]

/-- Complete interval computation for depth 15, residue 5023. -/
theorem bounds_15_5023 : exactInterval 15 5023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5023 : oddCount 5023 15 = 8 ∧ acceleratedOrbit 15 5023 = 1006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5023) = 3 ^ 8 * m + 1006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5023.1, data_15_5023.2]

/-- Complete interval computation for depth 15, residue 5024. -/
theorem bounds_15_5024 : exactInterval 15 5024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5024 : oddCount 5024 15 = 5 ∧ acceleratedOrbit 15 5024 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5024) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5024.1, data_15_5024.2]

/-- Complete interval computation for depth 15, residue 5025. -/
theorem bounds_15_5025 : exactInterval 15 5025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5025 : oddCount 5025 15 = 9 ∧ acceleratedOrbit 15 5025 = 3023 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5025) = 3 ^ 9 * m + 3023 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5025.1, data_15_5025.2]

/-- Complete interval computation for depth 15, residue 5026. -/
theorem bounds_15_5026 : exactInterval 15 5026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5026 : oddCount 5026 15 = 7 ∧ acceleratedOrbit 15 5026 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5026) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5026.1, data_15_5026.2]

/-- Complete interval computation for depth 15, residue 5027. -/
theorem bounds_15_5027 : exactInterval 15 5027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5027 : oddCount 5027 15 = 7 ∧ acceleratedOrbit 15 5027 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5027) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5027.1, data_15_5027.2]

/-- Complete interval computation for depth 15, residue 5028. -/
theorem bounds_15_5028 : exactInterval 15 5028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5028 : oddCount 5028 15 = 6 ∧ acceleratedOrbit 15 5028 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5028) = 3 ^ 6 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5028.1, data_15_5028.2]

/-- Complete interval computation for depth 15, residue 5029. -/
theorem bounds_15_5029 : exactInterval 15 5029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5029 : oddCount 5029 15 = 6 ∧ acceleratedOrbit 15 5029 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5029) = 3 ^ 6 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5029.1, data_15_5029.2]

/-- Complete interval computation for depth 15, residue 5030. -/
theorem bounds_15_5030 : exactInterval 15 5030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5030 : oddCount 5030 15 = 6 ∧ acceleratedOrbit 15 5030 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5030) = 3 ^ 6 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5030.1, data_15_5030.2]

/-- Complete interval computation for depth 15, residue 5031. -/
theorem bounds_15_5031 : exactInterval 15 5031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5031 : oddCount 5031 15 = 10 ∧ acceleratedOrbit 15 5031 = 9071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5031) = 3 ^ 10 * m + 9071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5031.1, data_15_5031.2]

/-- Complete interval computation for depth 15, residue 5032. -/
theorem bounds_15_5032 : exactInterval 15 5032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5032 : oddCount 5032 15 = 5 ∧ acceleratedOrbit 15 5032 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5032) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5032.1, data_15_5032.2]

/-- Complete interval computation for depth 15, residue 5033. -/
theorem bounds_15_5033 : exactInterval 15 5033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5033 : oddCount 5033 15 = 10 ∧ acceleratedOrbit 15 5033 = 9073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5033) = 3 ^ 10 * m + 9073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5033.1, data_15_5033.2]

/-- Complete interval computation for depth 15, residue 5034. -/
theorem bounds_15_5034 : exactInterval 15 5034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5034 : oddCount 5034 15 = 5 ∧ acceleratedOrbit 15 5034 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5034) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5034.1, data_15_5034.2]

/-- Complete interval computation for depth 15, residue 5035. -/
theorem bounds_15_5035 : exactInterval 15 5035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5035 : oddCount 5035 15 = 8 ∧ acceleratedOrbit 15 5035 = 1009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5035) = 3 ^ 8 * m + 1009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5035.1, data_15_5035.2]

/-- Complete interval computation for depth 15, residue 5036. -/
theorem bounds_15_5036 : exactInterval 15 5036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5036 : oddCount 5036 15 = 8 ∧ acceleratedOrbit 15 5036 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5036) = 3 ^ 8 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5036.1, data_15_5036.2]

/-- Complete interval computation for depth 15, residue 5037. -/
theorem bounds_15_5037 : exactInterval 15 5037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5037 : oddCount 5037 15 = 8 ∧ acceleratedOrbit 15 5037 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5037) = 3 ^ 8 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5037.1, data_15_5037.2]

/-- Complete interval computation for depth 15, residue 5038. -/
theorem bounds_15_5038 : exactInterval 15 5038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5038 : oddCount 5038 15 = 8 ∧ acceleratedOrbit 15 5038 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5038) = 3 ^ 8 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5038.1, data_15_5038.2]

/-- Complete interval computation for depth 15, residue 5039. -/
theorem bounds_15_5039 : exactInterval 15 5039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5039 : oddCount 5039 15 = 7 ∧ acceleratedOrbit 15 5039 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5039) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5039.1, data_15_5039.2]

/-- Complete interval computation for depth 15, residue 5040. -/
theorem bounds_15_5040 : exactInterval 15 5040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5040 : oddCount 5040 15 = 5 ∧ acceleratedOrbit 15 5040 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5040) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5040.1, data_15_5040.2]

/-- Complete interval computation for depth 15, residue 5041. -/
theorem bounds_15_5041 : exactInterval 15 5041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5041 : oddCount 5041 15 = 5 ∧ acceleratedOrbit 15 5041 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5041) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5041.1, data_15_5041.2]

/-- Complete interval computation for depth 15, residue 5042. -/
theorem bounds_15_5042 : exactInterval 15 5042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5042 : oddCount 5042 15 = 5 ∧ acceleratedOrbit 15 5042 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5042) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5042.1, data_15_5042.2]

/-- Complete interval computation for depth 15, residue 5043. -/
theorem bounds_15_5043 : exactInterval 15 5043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5043 : oddCount 5043 15 = 5 ∧ acceleratedOrbit 15 5043 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5043) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5043.1, data_15_5043.2]

/-- Complete interval computation for depth 15, residue 5044. -/
theorem bounds_15_5044 : exactInterval 15 5044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5044 : oddCount 5044 15 = 5 ∧ acceleratedOrbit 15 5044 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5044) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5044.1, data_15_5044.2]

/-- Complete interval computation for depth 15, residue 5045. -/
theorem bounds_15_5045 : exactInterval 15 5045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5045 : oddCount 5045 15 = 5 ∧ acceleratedOrbit 15 5045 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5045) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5045.1, data_15_5045.2]

end Collatz.Research.PassageAtlas.Batch0154
