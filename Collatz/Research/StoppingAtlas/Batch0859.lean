import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0859

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6010. -/
theorem bounds_13_6010 : exactInterval 13 6010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6010 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6010) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6010 : oddCount 6010 13 = 8 ∧ acceleratedOrbit 13 6010 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6010 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6010) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6010.1, data_13_6010.2]

/-- Complete interval computation for depth 13, residue 6011. -/
theorem bounds_13_6011 : exactInterval 13 6011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6011 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6011) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6011 : oddCount 6011 13 = 8 ∧ acceleratedOrbit 13 6011 = 4816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6011 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6011) = 3 ^ 8 * m + 4816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6011.1, data_13_6011.2]

/-- Complete interval computation for depth 13, residue 6012. -/
theorem bounds_13_6012 : exactInterval 13 6012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6012 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6012) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6012 : oddCount 6012 13 = 8 ∧ acceleratedOrbit 13 6012 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6012 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6012) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6012.1, data_13_6012.2]

/-- Complete interval computation for depth 13, residue 6013. -/
theorem bounds_13_6013 : exactInterval 13 6013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6013 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6013) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6013 : oddCount 6013 13 = 8 ∧ acceleratedOrbit 13 6013 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6013 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6013) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6013.1, data_13_6013.2]

/-- Complete interval computation for depth 13, residue 6014. -/
theorem bounds_13_6014 : exactInterval 13 6014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6014 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6014) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6014 : oddCount 6014 13 = 9 ∧ acceleratedOrbit 13 6014 = 14455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6014 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6014) = 3 ^ 9 * m + 14455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6014.1, data_13_6014.2]

/-- Complete interval computation for depth 13, residue 6015. -/
theorem bounds_13_6015 : exactInterval 13 6015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6015 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6015) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6015 : oddCount 6015 13 = 9 ∧ acceleratedOrbit 13 6015 = 14455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6015 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6015) = 3 ^ 9 * m + 14455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6015.1, data_13_6015.2]

/-- Complete interval computation for depth 13, residue 6016. -/
theorem bounds_13_6016 : exactInterval 13 6016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6016 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6016) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6016 : oddCount 6016 13 = 5 ∧ acceleratedOrbit 13 6016 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6016 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6016) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6016.1, data_13_6016.2]

/-- Complete interval computation for depth 13, residue 6017. -/
theorem bounds_13_6017 : exactInterval 13 6017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6017 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6017) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6017 : oddCount 6017 13 = 8 ∧ acceleratedOrbit 13 6017 = 4823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6017 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6017) = 3 ^ 8 * m + 4823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6017.1, data_13_6017.2]

/-- Complete interval computation for depth 13, residue 6018. -/
theorem bounds_13_6018 : exactInterval 13 6018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6018 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6018) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6018 : oddCount 6018 13 = 7 ∧ acceleratedOrbit 13 6018 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6018 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6018) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6018.1, data_13_6018.2]

/-- Complete interval computation for depth 13, residue 6019. -/
theorem bounds_13_6019 : exactInterval 13 6019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6019 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6019) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6019 : oddCount 6019 13 = 7 ∧ acceleratedOrbit 13 6019 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6019 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6019) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6019.1, data_13_6019.2]

/-- Complete interval computation for depth 13, residue 6020. -/
theorem bounds_13_6020 : exactInterval 13 6020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6020 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6020) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6020 : oddCount 6020 13 = 7 ∧ acceleratedOrbit 13 6020 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6020 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6020) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6020.1, data_13_6020.2]

/-- Complete interval computation for depth 13, residue 6021. -/
theorem bounds_13_6021 : exactInterval 13 6021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6021 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6021) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6021 : oddCount 6021 13 = 7 ∧ acceleratedOrbit 13 6021 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6021 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6021) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6021.1, data_13_6021.2]

/-- Complete interval computation for depth 13, residue 6022. -/
theorem bounds_13_6022 : exactInterval 13 6022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6022 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6022) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6022 : oddCount 6022 13 = 7 ∧ acceleratedOrbit 13 6022 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6022 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6022) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6022.1, data_13_6022.2]

/-- Complete interval computation for depth 13, residue 6023. -/
theorem bounds_13_6023 : exactInterval 13 6023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6023 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6023) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6023 : oddCount 6023 13 = 7 ∧ acceleratedOrbit 13 6023 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6023 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6023) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6023.1, data_13_6023.2]

/-- Complete interval computation for depth 13, residue 6024. -/
theorem bounds_13_6024 : exactInterval 13 6024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6024 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6024) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6024 : oddCount 6024 13 = 3 ∧ acceleratedOrbit 13 6024 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6024 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6024) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6024.1, data_13_6024.2]

/-- Complete interval computation for depth 13, residue 6025. -/
theorem bounds_13_6025 : exactInterval 13 6025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6025 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6025) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6025 : oddCount 6025 13 = 7 ∧ acceleratedOrbit 13 6025 = 1609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6025 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6025) = 3 ^ 7 * m + 1609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6025.1, data_13_6025.2]

end Collatz.Research.StoppingAtlas.Batch0859
