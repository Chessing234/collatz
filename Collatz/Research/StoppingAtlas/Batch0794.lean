import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0794

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5012. -/
theorem bounds_13_5012 : exactInterval 13 5012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5012 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5012) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5012 : oddCount 5012 13 = 6 ∧ acceleratedOrbit 13 5012 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5012 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5012) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5012.1, data_13_5012.2]

/-- Complete interval computation for depth 13, residue 5013. -/
theorem bounds_13_5013 : exactInterval 13 5013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5013 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5013) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5013 : oddCount 5013 13 = 6 ∧ acceleratedOrbit 13 5013 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5013 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5013) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5013.1, data_13_5013.2]

/-- Complete interval computation for depth 13, residue 5014. -/
theorem bounds_13_5014 : exactInterval 13 5014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5014 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5014) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5014 : oddCount 5014 13 = 5 ∧ acceleratedOrbit 13 5014 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5014 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5014) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5014.1, data_13_5014.2]

/-- Complete interval computation for depth 13, residue 5015. -/
theorem bounds_13_5015 : exactInterval 13 5015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5015 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5015) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5015 : oddCount 5015 13 = 5 ∧ acceleratedOrbit 13 5015 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5015 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5015) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5015.1, data_13_5015.2]

/-- Complete interval computation for depth 13, residue 5016. -/
theorem bounds_13_5016 : exactInterval 13 5016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5016 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5016) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5016 : oddCount 5016 13 = 6 ∧ acceleratedOrbit 13 5016 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5016 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5016) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5016.1, data_13_5016.2]

/-- Complete interval computation for depth 13, residue 5017. -/
theorem bounds_13_5017 : exactInterval 13 5017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5017 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5017) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5017 : oddCount 5017 13 = 5 ∧ acceleratedOrbit 13 5017 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5017 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5017) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5017.1, data_13_5017.2]

/-- Complete interval computation for depth 13, residue 5018. -/
theorem bounds_13_5018 : exactInterval 13 5018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5018 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5018) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5018 : oddCount 5018 13 = 6 ∧ acceleratedOrbit 13 5018 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5018 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5018) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5018.1, data_13_5018.2]

/-- Complete interval computation for depth 13, residue 5019. -/
theorem bounds_13_5019 : exactInterval 13 5019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5019 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5019) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5019 : oddCount 5019 13 = 8 ∧ acceleratedOrbit 13 5019 = 4022 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5019 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5019) = 3 ^ 8 * m + 4022 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5019.1, data_13_5019.2]

/-- Complete interval computation for depth 13, residue 5020. -/
theorem bounds_13_5020 : exactInterval 13 5020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5020 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5020) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5020 : oddCount 5020 13 = 8 ∧ acceleratedOrbit 13 5020 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5020 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5020) = 3 ^ 8 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5020.1, data_13_5020.2]

/-- Complete interval computation for depth 13, residue 5021. -/
theorem bounds_13_5021 : exactInterval 13 5021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5021 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5021) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5021 : oddCount 5021 13 = 8 ∧ acceleratedOrbit 13 5021 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5021 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5021) = 3 ^ 8 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5021.1, data_13_5021.2]

/-- Complete interval computation for depth 13, residue 5022. -/
theorem bounds_13_5022 : exactInterval 13 5022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5022 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5022) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5022 : oddCount 5022 13 = 8 ∧ acceleratedOrbit 13 5022 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5022 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5022) = 3 ^ 8 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5022.1, data_13_5022.2]

/-- Complete interval computation for depth 13, residue 5023. -/
theorem bounds_13_5023 : exactInterval 13 5023 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5023 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5023) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5023 : oddCount 5023 13 = 8 ∧ acceleratedOrbit 13 5023 = 4024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5023 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5023) = 3 ^ 8 * m + 4024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5023.1, data_13_5023.2]

/-- Complete interval computation for depth 13, residue 5024. -/
theorem bounds_13_5024 : exactInterval 13 5024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5024 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5024) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5024 : oddCount 5024 13 = 5 ∧ acceleratedOrbit 13 5024 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5024 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5024) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5024.1, data_13_5024.2]

/-- Complete interval computation for depth 13, residue 5025. -/
theorem bounds_13_5025 : exactInterval 13 5025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5025 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5025) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5025 : oddCount 5025 13 = 7 ∧ acceleratedOrbit 13 5025 = 1343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5025 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5025) = 3 ^ 7 * m + 1343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5025.1, data_13_5025.2]

/-- Complete interval computation for depth 13, residue 5026. -/
theorem bounds_13_5026 : exactInterval 13 5026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5026 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5026) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5026 : oddCount 5026 13 = 6 ∧ acceleratedOrbit 13 5026 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5026 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5026) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5026.1, data_13_5026.2]

end Collatz.Research.StoppingAtlas.Batch0794
